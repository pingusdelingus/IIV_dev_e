#!/usr/bin/env python3

import sys
import os
import re
from typing import Dict, List, Set, Tuple, Optional
import argparse
from antlr4 import *

from TPTPLexer import TPTPLexer
from TPTPParser import TPTPParser
from TPTPListener import TPTPListener
from antlr4.tree.Trees import Trees
from antlr4 import ParseTreeWalker


class TPTPModalExtractor(TPTPListener):
    def __init__(self):
        self.declarations = []  # Type declarations
        self.worlds = set()  # World names
        
        self.explicit_edges: List[Tuple[str, str, bool]] = []
        
        self.in_type_decl = False
        
        self.universal_accessibility: bool = False
        self.universal_polarity: bool = True 

        self.local_world: Optional[str] = None 
        self.extra_conjuncts = [] 
        self.interpretation_worlds_name = "model_worlds" 
        
    def get_argument_term_contexts(self, args_ctx):
            terms = []
            if args_ctx.tff_term():
                terms.append(args_ctx.tff_term())
            comma_terms = args_ctx.comma_tff_term()
            if comma_terms:
                if isinstance(comma_terms, list):
                    for ct in comma_terms:
                        if ct.tff_term():
                            terms.append(ct.tff_term())
                else:
                    if comma_terms.tff_term():
                        terms.append(comma_terms.tff_term())
            return terms

    def term_is_variable(self, term_ctx) -> bool:
        try:
            var_node = (term_ctx.tff_logic_formula()
                        .tff_unitary_formula()
                        .txf_unitary_formula()
                        .variable())
            if var_node:
                return True
        except Exception:
            pass
        return False

    def get_original_text(self, ctx):
        if ctx.start and ctx.stop:
            stream = ctx.start.getTokenSource()
            if hasattr(stream, '_input'):
                input_stream = stream._input
                start_idx = ctx.start.start
                stop_idx = ctx.stop.stop
                return input_stream.getText(start_idx, stop_idx)
        return ctx.getText()

    def get_polarity(self, ctx) -> bool:
        p = ctx.parentCtx
        steps = 0
        # looking for Tff_prefix_unaryContext which holds the '~'
        while p and steps < 8:
            if isinstance(p, TPTPParser.Tff_prefix_unaryContext):
                if p.tff_unary_connective() and p.tff_unary_connective().getText() == '~':
                    return False # Found a negation
            
            # picking up negations that belong to parent clauses.
            if isinstance(p, TPTPParser.Tff_quantified_formulaContext):
                break
            
            p = p.parentCtx
            steps += 1
        return True

    def enterTff_annotated(self, ctx):
        formula_text = self.get_original_text(ctx)
        role = ctx.formula_role().getText() if ctx.formula_role() else None
        
        if role == "type":
            self.in_type_decl = True
            self.declarations.append(formula_text)
            
            if ctx.tff_formula() and ctx.tff_formula().tff_atom_typing():
                typing = ctx.tff_formula().tff_atom_typing()
                if typing.tff_top_level_type():
                    type_text = typing.tff_top_level_type().getText()
                    if type_text == "$world":
                        if typing.untyped_atom():
                            world_name = typing.untyped_atom().getText()
                            self.worlds.add(world_name)
        
        elif role == "interpretation-worlds":
            if ctx.name():
                self.interpretation_worlds_name = ctx.name().getText()
                
            class ConjunctFinder(TPTPListener):
                def __init__(self, extractor):
                    self.extractor = extractor
                
                def enterTff_defined_plain(self, ctx: TPTPParser.Tff_defined_plainContext):
                    if ctx.defined_functor() and ctx.defined_functor().getText().startswith("$"):
                        text = self.extractor.get_original_text(ctx)
                        # We handle accessible and local world manually, store others (like $distinct)
                        if "$accessible_world" not in text and "$local_world" not in text:
                            self.extractor.extra_conjuncts.append(text)
            
            if ctx.tff_formula():
                walker = ParseTreeWalker()
                finder = ConjunctFinder(self)
                walker.walk(finder, ctx.tff_formula())

    def exitTff_annotated(self, ctx):
        if self.in_type_decl:
            self.in_type_decl = False

    def enterTff_defined_infix(self, ctx):
        pred = ctx.defined_infix_pred()
        if pred and pred.infix_equality():
            lhs = ctx.tff_unitary_term(0).getText()
            rhs = ctx.tff_unitary_term(1).getText()
            
            if lhs == "$local_world":
                self.local_world = rhs
                self.worlds.add(rhs)
            elif rhs == "$local_world":
                self.local_world = lhs
                self.worlds.add(lhs)
    
    def enterTff_defined_plain(self, ctx):
        if ctx.defined_functor():
            func_name = ctx.defined_functor().getText()
            
            if func_name == "$accessible_world" and ctx.tff_arguments():
                args = ctx.tff_arguments()
                term_ctxs = self.get_argument_term_contexts(args)

                is_positive = self.get_polarity(ctx)

                # CASE 1: Universal Quantifier (![W,V]: $accessible_world(W,V))
                if self.both_args_universally_quantified_worlds(ctx, term_ctxs):
                    self.universal_accessibility = True
                    self.universal_polarity = is_positive
                    return

                # CASE 2: Explicit Edge ($accessible_world(w1, w2))
                if len(term_ctxs) >= 2:
                    from_world_ctx = term_ctxs[0]
                    to_world_ctx = term_ctxs[1]

                    if not self.term_is_variable(from_world_ctx) and not self.term_is_variable(to_world_ctx):
                        from_world_txt = self.get_term_text(from_world_ctx)
                        to_world_txt = self.get_term_text(to_world_ctx)

                        # Store the edge AND its polarity
                        self.explicit_edges.append((from_world_txt, to_world_txt, is_positive))

                        self.worlds.add(from_world_txt)
                        self.worlds.add(to_world_txt)
    
    def get_term_text(self, term_ctx):
        try:
            var_node = (term_ctx.tff_logic_formula()
                        .tff_unitary_formula()
                        .txf_unitary_formula()
                        .variable())
            if var_node:
                return var_node.getText()
        except Exception:
            pass 

        try:
            const_node = (term_ctx.tff_logic_formula()
                          .tff_unitary_formula()
                          .tff_atomic_formula()
                          .tff_plain_atomic()
                          .constant())
            if const_node:
                return const_node.getText()
        except Exception:
            pass 
            
        try:
            def_const_node = (term_ctx.tff_logic_formula()
                              .tff_unitary_formula()
                              .tff_atomic_formula()
                              .tff_defined_atomic()
                              .tff_defined_plain()
                              .defined_constant())
            if def_const_node:
                return def_const_node.getText()
        except Exception:
            pass
        
        return term_ctx.getText()
    
    def both_args_universally_quantified_worlds(self, ctx, arg_term_ctxs) -> bool:
        if len(arg_term_ctxs) < 2:
            return False
        lhs, rhs = arg_term_ctxs[0], arg_term_ctxs[1]
        if not (self.term_is_variable(lhs) and self.term_is_variable(rhs)):
            return False
        vL = self.get_term_text(lhs)
        vR = self.get_term_text(rhs)
        return self.is_universally_quantified_world(ctx, vL) and self.is_universally_quantified_world(ctx, vR)

    def is_universally_quantified_world(self, ctx, var_name):
        parent = ctx.parentCtx
        while parent:
            if isinstance(parent, TPTPParser.Tff_quantified_formulaContext):
                if parent.tff_quantifier() and parent.tff_quantifier().getText() == "!":
                    var_list = parent.tff_variable_list()
                    if var_list:
                        variables = self.extract_typed_variables(var_list)
                        for var, var_type in variables:
                            if var == var_name and var_type == "$world":
                                return True
            parent = parent.parentCtx
        return False
    
    def extract_typed_variables(self, var_list_ctx):
        variables = []
        def get_var_info(var_ctx):
            if not var_ctx: return None
            if hasattr(var_ctx, 'tff_typed_variable') and callable(var_ctx.tff_typed_variable):
                typed_var = var_ctx.tff_typed_variable()
                if typed_var and typed_var.variable() and typed_var.tff_atomic_type():
                    return (typed_var.variable().getText(), typed_var.tff_atomic_type().getText())
            if hasattr(var_ctx, 'variable') and callable(var_ctx.variable):
                 var = var_ctx.variable()
                 if var: return (var.getText(), None)
            return None

        current_list = var_list_ctx
        while current_list:
            var_ctx = None
            if hasattr(current_list, 'tff_variable') and callable(current_list.tff_variable):
                var_ctx = current_list.tff_variable()
            info = get_var_info(var_ctx)
            if info: variables.append(info)
            if hasattr(current_list, 'tff_variable_list') and callable(current_list.tff_variable_list):
                current_list = current_list.tff_variable_list()
            else: current_list = None 
        return variables


class TPTPModalParserANTLR:
    def __init__(self):
        self.block_regex = re.compile(
            r"tff\(([^,]+)\s*,\s*interpretation-worlds\s*,\s*(.*?)\)\s*\.\s*$",
            re.MULTILINE | re.DOTALL
        )

    def run_antlr_extractor(self, filepath: str) -> TPTPModalExtractor:
        input_stream = FileStream(filepath, encoding="utf-8")
        lexer = TPTPLexer(input_stream)
        stream = CommonTokenStream(lexer)
        parser = TPTPParser(stream)
        tree = parser.tptp_file()
        walker = ParseTreeWalker()
        extractor = TPTPModalExtractor()
        walker.walk(extractor, tree)
        return extractor

    def get_expanded_file_content(self, filepath: str) -> Optional[str]:
        extractor = self.run_antlr_extractor(filepath)
        with open(filepath, 'r', encoding='utf-8') as f:
            raw_text = f.read()
        
        new_expanded_block = self.build_interpretation_block(extractor)
        
        if self.block_regex.search(raw_text):
            new_file_content = self.block_regex.sub(new_expanded_block, raw_text, count=1)
            return new_file_content
        else:
            return raw_text

    def build_interpretation_block(self, extractor: TPTPModalExtractor) -> str:
            block_name = extractor.interpretation_worlds_name
            worlds = sorted(extractor.worlds)

            enum_line = None
            if worlds:
                disj = " | ".join([f"W = {w}" for w in worlds])
                enum_line = f"! [W: $world] : ( {disj} )"

            local_line = None
            if extractor.local_world:
                local_line = f"$local_world = {extractor.local_world}"

            acc_lines = []
            
            if extractor.universal_accessibility and worlds:
                expanded_edges = self.expand_accessibility(worlds)
                for (u, v) in expanded_edges:
                    if extractor.universal_polarity:
                        acc_lines.append(f"$accessible_world({u},{v})")
                    else:
                        acc_lines.append(f"~ $accessible_world({u},{v})")

            for (u, v, is_positive) in extractor.explicit_edges:
                if is_positive:
                    acc_lines.append(f"$accessible_world({u},{v})")
                else:
                    acc_lines.append(f"~ $accessible_world({u},{v})")

            acc_lines = sorted(list(set(acc_lines)))

            body_parts = []
            if enum_line:
                body_parts.append(enum_line)
            if extractor.extra_conjuncts:
                body_parts.extend(sorted(extractor.extra_conjuncts))
            if local_line:
                body_parts.append(local_line)
            body_parts.extend(acc_lines)

            body = "\n    & ".join(body_parts) if body_parts else ""

            return (
                f"tff({block_name},interpretation-worlds,\n"
                f"    ( {body}\n"
                f"    ) )."
            )

    def expand_accessibility(self, worlds: List[str]) -> List[Tuple[str, str]]:
       clauses: List[Tuple[str, str]] = []
       for i in worlds:
           for j in worlds:
               clauses.append((i, j))
       return clauses

def make_html_friendly(file_text: str) -> str:
    return file_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")




def main():
    parser = argparse.ArgumentParser(
        description='Expands universal accessibility in TPTP modal logic files. \n usage: python3 ExpandKripeInterpretation_V2 file_name output_path htmlFriendly? printToSTDOUT?'
    )
    parser.add_argument('file', help='Input TPTP file (.p or .tptp extension)')
    parser.add_argument('output_path', help="Output directory OR full file path")
    parser.add_argument('htmlFriendly', help="1 for html sanitization, 0 for plain")
    parser.add_argument('printToSTDOUT', help="1 for printing to stdout , 0 for no printing")

    args = parser.parse_args()

    tptp_parser = TPTPModalParserANTLR()

    try:
        expanded_content = tptp_parser.get_expanded_file_content(args.file)

        if expanded_content is None:
            print(f"Error: Could not find 'interpretation-worlds' block in {args.file}", file=sys.stderr)
            sys.exit(1)

        if args.htmlFriendly == '1':
            final_output = make_html_friendly(expanded_content)
        else:
            final_output = expanded_content

        if os.path.isdir(args.output_path):
            base_name = os.path.basename(args.file)
            name_without_ext, ext = os.path.splitext(base_name)
            out_dir = os.path.abspath(args.output_path)
            new_filename = os.path.join(out_dir, f"{name_without_ext}_EXPANDED.s") 
        else:
            new_filename = args.output_path
            os.makedirs(os.path.dirname(os.path.abspath(new_filename)), exist_ok=True)

        with open(new_filename, 'w', encoding='utf-8') as f:
            f.write(final_output)


        print("% SZS status Success")
        if args.printToSTDOUT == '1':
            print(final_output)
#        print(f"Successfully wrote expanded file to: {new_filename}")

    except FileNotFoundError:
        print(f"Error: File '{args.file}' not found.", file=sys.stderr)
        print("% SZS status NoSuccess")
        sys.exit(1)
    except Exception as e:
        print(f"Error processing file: {e}", file=sys.stderr)
        print("% SZS status NoSuccess")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
