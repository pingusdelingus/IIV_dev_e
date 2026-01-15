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

    def term_constant_text(self, term_ctx) -> Optional[str]:
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
        return None

    def both_args_universally_quantified_worlds(self, ctx, arg_term_ctxs) -> bool:
        if len(arg_term_ctxs) < 2:
            return False
        lhs, rhs = arg_term_ctxs[0], arg_term_ctxs[1]
        if not (self.term_is_variable(lhs) and self.term_is_variable(rhs)):
            return False
        vL = self.get_term_text(lhs)
        vR = self.get_term_text(rhs)
        return self.is_universally_quantified_world(ctx, vL) and self.is_universally_quantified_world(ctx, vR)
    
    def __init__(self):
        self.declarations = []  # Type declarations
        self.worlds = set()  # World names
        self.accessible_worlds = {}  # Accessibility relations
        self.in_type_decl = False
        self.universal_accessibility: bool = False
        self.local_world: Optional[str] = None # This will be set externally
        self.extra_conjuncts = [] # To store things like $distinct
        self.interpretation_worlds_name = "model_worlds" # Default
        
    def get_original_text(self, ctx):
        if ctx.start and ctx.stop:
            stream = ctx.start.getTokenSource()
            if hasattr(stream, '_input'):
                input_stream = stream._input
                start_idx = ctx.start.start
                stop_idx = ctx.stop.stop
                return input_stream.getText(start_idx, stop_idx)
        return ctx.getText()

    def enterTff_annotated(self, ctx):
        """Enter a TFF annotated formula."""
        formula_text = self.get_original_text(ctx)
        role = ctx.formula_role().getText() if ctx.formula_role() else None
        
        if role == "type":
            self.in_type_decl = True
            self.declarations.append(formula_text)
            
            # check for world declarations
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
                        if "$accessible_world" not in text:
                            self.extractor.extra_conjuncts.append(text)
            
            if ctx.tff_formula():
                walker = ParseTreeWalker()
                finder = ConjunctFinder(self)
                walker.walk(finder, ctx.tff_formula())

    def exitTff_annotated(self, ctx):
        if self.in_type_decl:
            self.in_type_decl = False

    def enterTff_defined_infix(self, ctx):
        """
        $local_world is handled by a simple string search.
        """
        pass
    
    def enterTff_defined_plain(self, ctx):
        """Check for $accessible_world."""
        if ctx.defined_functor():
            func_name = ctx.defined_functor().getText()
            
            if func_name == "$accessible_world" and ctx.tff_arguments():
                args = ctx.tff_arguments()
                term_ctxs = self.get_argument_term_contexts(args)

                if self.both_args_universally_quantified_worlds(ctx, term_ctxs):
                    
                    # --- NEW CHECK for negation ---
                    is_negated = False
                    parent = ctx.parentCtx # tff_plain_atomic
                    
                    # Walk up the tree to check for a tilde
                    if parent and isinstance(parent, TPTPParser.Tff_plain_atomicContext):
                        parent = parent.parentCtx # tff_atomic_formula
                    if parent and isinstance(parent, TPTPParser.Tff_atomic_formulaContext):
                        parent = parent.parentCtx # tff_unitary_formula
                    if parent and isinstance(parent, TPTPParser.Tff_unitary_formulaContext):
                        parent = parent.parentCtx # tff_unit_formula
                    if parent and isinstance(parent, TPTPParser.Tff_unit_formulaContext):
                        parent = parent.parentCtx # tff_preunit_formula or tff_unary_formula

                    # Check if the parent is a unary negation
                    if (parent and
                        (isinstance(parent, TPTPParser.Tff_unary_formulaContext) or
                         isinstance(parent, TPTPParser.Tff_prefix_unaryContext)) and
                        hasattr(parent, 'tff_unary_connective') and
                        parent.tff_unary_connective() and
                        parent.tff_unary_connective().getText() == '~'):
                        
                        is_negated = True
                    
                    if not is_negated:
                        self.universal_accessibility = True
                    # --- END NEW CHECK ---
                        
                    return

                if len(term_ctxs) >= 2:
                    from_world_ctx = term_ctxs[0]
                    to_world_ctx = term_ctxs[1]

                    if not self.term_is_variable(from_world_ctx) and not self.term_is_variable(to_world_ctx):
                        from_world_txt = self.get_term_text(from_world_ctx)
                        to_world_txt = self.get_term_text(to_world_ctx)

                        if from_world_txt not in self.accessible_worlds:
                            self.accessible_worlds[from_world_txt] = []
                        self.accessible_worlds[from_world_txt].append(to_world_txt)

                        self.worlds.add(from_world_txt)
                        self.worlds.add(to_world_txt)
    
    def get_term_text(self, term_ctx):
        """Extract text from a term context, trying all paths."""
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
    
    def is_universally_quantified_world(self, ctx, var_name):
        """Check if a variable is universally quantified as a world in parent context."""
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
        """Extract (name, type) tuples from a tff_variable_list context."""
        variables = []
        
        def get_var_info(var_ctx):
            if not var_ctx:
                return None
            if hasattr(var_ctx, 'tff_typed_variable') and callable(var_ctx.tff_typed_variable):
                typed_var = var_ctx.tff_typed_variable()
                if typed_var and typed_var.variable() and typed_var.tff_atomic_type():
                    var_name = typed_var.variable().getText()
                    var_type = typed_var.tff_atomic_type().getText()
                    return (var_name, var_type)
            if hasattr(var_ctx, 'variable') and callable(var_ctx.variable):
                 var = var_ctx.variable()
                 if var:
                    return (var.getText(), None) # Untyped
            return None

        current_list = var_list_ctx
        while current_list:
            var_ctx = None
            if hasattr(current_list, 'tff_variable') and callable(current_list.tff_variable):
                var_ctx = current_list.tff_variable()
            
            info = get_var_info(var_ctx)
            if info:
                variables.append(info)
            
            if hasattr(current_list, 'tff_variable_list') and callable(current_list.tff_variable_list):
                current_list = current_list.tff_variable_list()
            else:
                current_list = None 

        return variables


class TPTPModalParserANTLR:
    
    def __init__(self):
        # Regex to find the original interpretation-worlds block for replacement
        self.block_regex = re.compile(
            r"tff\(([^,]+)\s*,\s*interpretation-worlds\s*,\s*(.*?)\)\s*\.\s*$",
            re.MULTILINE | re.DOTALL
        )

    def find_local_world_simple(self, raw_text: str) -> Optional[str]:
        """Manually parse the file text to find the local world."""
        try:
            start_index = raw_text.find("interpretation-worlds")
            if start_index == -1: return None
            end_index = raw_text.find(").", start_index)
            if end_index == -1: return None
            block_text = raw_text[start_index:end_index]
            
            lw_key = "$local_world"
            lw_index = block_text.find(lw_key)
            if lw_index == -1: return None
            eq_index = block_text.find("=", lw_index)
            if eq_index == -1: return None

            world_name = ""
            i = eq_index + 1
            while i < len(block_text):
                char = block_text[i]
                if char.isspace():
                    if world_name: break
                    else:
                        i += 1
                        continue
                
                if char.isalnum() or char == '_':
                    world_name += char
                else:
                    if world_name: break
                    else: return None
                i += 1
            
            if world_name:
                return world_name
        except Exception:
            pass
        return None

    def run_antlr_extractor(self, filepath: str) -> TPTPModalExtractor:
        """Helper to run the ANTLR extractor just once."""
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
        """
        Generates the full, expanded file content as a string.
        Returns None if the interpretation-worlds block wasn't found.
        """
        
        # 1. Run ANTLR for types, $distinct, accessibility, etc.
        extractor = self.run_antlr_extractor(filepath)
        
        # 2. Run simple string search for $local_world
        with open(filepath, 'r', encoding='utf-8') as f:
            raw_text = f.read()
        local_world_name = self.find_local_world_simple(raw_text)
        
        # 3. Inject the findings into the extractor
        if local_world_name:
            extractor.local_world = local_world_name
            extractor.worlds.add(local_world_name)

        # 4. Build the new, expanded block
        new_expanded_block = self.build_interpretation_block(extractor)
        
        # 5. Replace the old block with the new one
        if self.block_regex.search(raw_text):
            new_file_content = self.block_regex.sub(new_expanded_block, raw_text, count=1)
            return new_file_content
        else:
            # Block not found, return original text
            return raw_text

    def build_interpretation_block(self, extractor: TPTPModalExtractor) -> str:
            """Pretty-print a single interpretation-worlds block with expansions."""
            block_name = extractor.interpretation_worlds_name
            worlds = sorted(extractor.worlds)

            enum_line = None
            if worlds:
                disj = " | ".join([f"W = {w}" for w in worlds])
                enum_line = f"! [W: $world] : ( {disj} )"

            local_line = None
            if extractor.local_world:
                local_line = f"$local_world = {extractor.local_world}"

            edges_set: Set[Tuple[str, str]] = set()
            if extractor.universal_accessibility and worlds:
                edges_set.update(self.expand_accessibility(worlds))
            for u, vs in extractor.accessible_worlds.items():
                for v in vs:
                    edges_set.add((u, v))
            acc_lines = [f"$accessible_world({u},{v})" for (u, v) in sorted(edges_set)]

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
       """Expand ![W,V] : $accessible_world(W,V) into all (world, world) pairs."""
       clauses: List[Tuple[str, str]] = []
       for i in worlds:
           for j in worlds:
               clauses.append((i, j))
       return clauses
    

def main():
    parser = argparse.ArgumentParser(
        description='Expands universal accessibility in TPTP modal logic files.'
    )
    parser.add_argument('file', help='Input TPTP file (.p or .tptp extension)')
    args = parser.parse_args()
    
    tptp_parser = TPTPModalParserANTLR()
    
    try:
        # --- 1. Generate the new file content ---
        expanded_content = tptp_parser.get_expanded_file_content(args.file)
        
        if expanded_content is None:
            print(f"Error: Could not find 'interpretation-worlds' block in {args.file}", file=sys.stderr)
            sys.exit(1)

        # --- 2. Print expanded content to stdout ---
        print(expanded_content)

        # --- 3. Write to new file ---
        base_name = os.path.basename(args.file)
        name_without_ext, ext = os.path.splitext(base_name)
        # We use .p as requested, which is a standard TPTP extension
        new_filename = f"{name_without_ext}_EXPANDED.p" 
        
        with open(new_filename, 'w', encoding='utf-8') as f:
            f.write(expanded_content)
            
        print(f"\n--- \nSuccessfully saved expanded file to: {new_filename}", file=sys.stderr)
    
    except FileNotFoundError:
        print(f"Error: File '{args.file}' not found.", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error processing file: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
