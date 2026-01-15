#!/usr/bin/env python3

import sys

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
            """Return a list of tff_term contexts in order."""
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
        """Check if a term is a variable by following the txf_unitary_formula path."""
        try:
            # Path V: tff_term -> tff_logic_formula -> tff_unitary_formula -> txf_unitary_formula -> variable
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
        """Return text of a constant by following the tff_plain_atomic path."""
        try:
            # Path C: tff_term -> tff_logic_formula -> tff_unitary_formula -> tff_atomic_formula -> tff_plain_atomic -> constant
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
        self.in_world_blocks = {}  # World -> content mapping
        self.accessible_worlds = {}  # Accessibility relations
        self.current_formula = None
        self.in_type_decl = False
        self.collecting_in_world = False
        self.current_world = None
        self.in_world_content = []  
        self.universal_accessibility: bool = False
        self.local_world: Optional[str] = None
        # --- NEW ---
        self.extra_conjuncts = [] # To store things like $distinct
        self.interpretation_worlds_name = "model_worlds" # Default
        
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
                        # extract world name
                        if typing.untyped_atom():
                            world_name = typing.untyped_atom().getText()
                            self.worlds.add(world_name)
        
        # --- NEW LOGIC to find $distinct and block name ---
        elif role == "interpretation-worlds":
            # Save the name, e.g., "model_worlds"
            if ctx.name():
                self.interpretation_worlds_name = ctx.name().getText()
                
            # Define a simple listener to find $distinct atoms
            class DistinctFinder(TPTPListener):
                def __init__(self, extractor):
                    self.extractor = extractor
                
                def enterTff_defined_plain(self, ctx: TPTPParser.Tff_defined_plainContext):
                    if ctx.defined_functor() and ctx.defined_functor().getText() == "$distinct":
                        # We found one! Save its original text.
                        text = self.extractor.get_original_text(ctx)
                        self.extractor.extra_conjuncts.append(text)
            
            # Walk the formula sub-tree with our special finder
            if ctx.tff_formula():
                walker = ParseTreeWalker()
                finder = DistinctFinder(self)
                walker.walk(finder, ctx.tff_formula())
        # --- END NEW LOGIC ---

    def exitTff_annotated(self, ctx):
        """Exit a TFF annotated formula."""
        if self.in_type_decl:
            self.in_type_decl = False

    def enterTff_defined_infix(self, ctx):
        """Catch equalities like $local_world = world_5 and harvest constants."""
        if not (hasattr(ctx, "defined_infix") and ctx.defined_infix()):
            return
        if ctx.defined_infix().getText() != "=":
            return

        # two terms
        if hasattr(ctx, "tff_term"):
            lhs = ctx.tff_term(0) if ctx.tff_term(0) else None
            rhs = ctx.tff_term(1) if ctx.tff_term(1) else None
        else:
            lhs = rhs = None

        if not lhs or not rhs:
            return

        lhs_txt = self.get_term_text(lhs)
        rhs_const = self.term_constant_text(rhs)
        lhs_const = self.term_constant_text(lhs)

        # $local_world = <const>
        if lhs_txt == "$local_world" and rhs_const:
            self.local_world = rhs_const
            self.worlds.add(rhs_const)

        # Harvest worlds from equalities
        if self.term_is_variable(lhs) and rhs_const:
            v = self.get_term_text(lhs)
            if self.is_universally_quantified_world(ctx, v):
                self.worlds.add(rhs_const)
        if self.term_is_variable(rhs) and lhs_const:
            v = self.get_term_text(rhs)
            if self.is_universally_quantified_world(ctx, v):
                self.worlds.add(lhs_const)
    
    def enterTff_defined_plain(self, ctx):
        """Check for $in_world and $accessible_world."""
        if ctx.defined_functor():
            func_name = ctx.defined_functor().getText()
            
            if func_name == "$in_world" and ctx.tff_arguments():
                # extract $in_world content
                args = ctx.tff_arguments()
                terms = self.get_argument_terms(args)
                
                if len(terms) >= 2:
                    world_arg = terms[0]
                    content = self.extract_in_world_content(ctx)
                    
                    # check if it's a specific world or a variable
                    if world_arg in self.worlds:
                        # specific world
                        if world_arg not in self.in_world_blocks:
                            self.in_world_blocks[world_arg] = []
                        self.in_world_blocks[world_arg].append(content)
                    else:
                        # could be a universally quantified variable
                        if self.is_universally_quantified_world(ctx, world_arg):
                            # add to all worlds
                            for world in self.worlds:
                                if world not in self.in_world_blocks:
                                    self.in_world_blocks[world] = []
                                self.in_world_blocks[world].append(content)
            
            elif func_name == "$accessible_world" and ctx.tff_arguments():
                args = ctx.tff_arguments()
                term_ctxs = self.get_argument_term_contexts(args)

                # Case A: universally quantified schema
                if self.both_args_universally_quantified_worlds(ctx, term_ctxs):
                    self.universal_accessibility = True
                    return

                # Case B: explicit edge
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
    
    def get_original_text(self, ctx):
        if ctx.start and ctx.stop:
            stream = ctx.start.getTokenSource()
            if hasattr(stream, '_input'):
                input_stream = stream._input
                start_idx = ctx.start.start
                stop_idx = ctx.stop.stop
                return input_stream.getText(start_idx, stop_idx)
        return ctx.getText()
    
    def get_argument_terms(self, args_ctx):
        """Extract argument terms from tff_arguments context."""
        terms = []
        
        # first term
        if args_ctx.tff_term():
            terms.append(self.get_term_text(args_ctx.tff_term()))
        
        # Additional terms
        comma_terms = args_ctx.comma_tff_term()
        if comma_terms:
            if isinstance(comma_terms, list):
                for ct in comma_terms:
                    if ct.tff_term():
                        terms.append(self.get_term_text(ct.tff_term()))
            else:
                if comma_terms.tff_term():
                    terms.append(self.get_term_text(comma_terms.tff_term()))
        
        return terms
    
    def get_term_text(self, term_ctx):
        """Extract text from a term context, trying the Variable path first, then the Constant path."""
        
        # Path V (Variable)
        try:
            var_node = (term_ctx.tff_logic_formula()
                        .tff_unitary_formula()
                        .txf_unitary_formula()
                        .variable())
            if var_node:
                return var_node.getText()
        except Exception:
            pass # Not a variable, try next path

        # Path C (Constant)
        try:
            const_node = (term_ctx.tff_logic_formula()
                          .tff_unitary_formula()
                          .tff_atomic_formula()
                          .tff_plain_atomic()
                          .constant())
            if const_node:
                return const_node.getText()
        except Exception:
            pass # Not a constant
        
        # Fallback
        return term_ctx.getText()
    
    def extract_in_world_content(self, ctx):
        """Extract the content within $in_world(W, ...) - just the ... part."""
        if not ctx.tff_arguments():
            return ""
        
        args = ctx.tff_arguments()
        
        comma_terms = args.comma_tff_term()
        if comma_terms:
            if isinstance(comma_terms, list) and comma_terms:
                content_ctx = comma_terms[0].tff_term() if comma_terms[0].tff_term() else comma_terms[0]
            else:
                content_ctx = comma_terms.tff_term() if comma_terms.tff_term() else comma_terms
            
            return self.get_original_text(content_ctx)
        
        return ""
    
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
            """Helper to extract info from a single tff_variable context."""
            if not var_ctx:
                return None
            
            # Path A: tff_variable -> tff_typed_variable -> ...
            if hasattr(var_ctx, 'tff_typed_variable') and callable(var_ctx.tff_typed_variable):
                typed_var = var_ctx.tff_typed_variable()
                if typed_var and typed_var.variable() and typed_var.tff_atomic_type():
                    var_name = typed_var.variable().getText()
                    var_type = typed_var.tff_atomic_type().getText()
                    return (var_name, var_type)
            
            # Path B: tff_variable -> variable (untyped)
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
            
            # Move to the next (recursive) list node
            if hasattr(current_list, 'tff_variable_list') and callable(current_list.tff_variable_list):
                current_list = current_list.tff_variable_list()
            else:
                current_list = None # This was the end of the list

        return variables


class TPTPModalParserANTLR:
    def process_file_new(self, filepath: str) -> Tuple[str, List[str]]:
        input_stream = FileStream(filepath, encoding="utf-8")
        lexer = TPTPLexer(input_stream)
        stream = CommonTokenStream(lexer)
        parser = TPTPParser(stream)

        tree = parser.tptp_file()

        walker = ParseTreeWalker()
        extractor = TPTPModalExtractor()
        walker.walk(extractor, tree)

        # name to use in tff(.., interpretation-worlds, ...)
        # We will now use the name found by the extractor
        name = extractor.interpretation_worlds_name

        block = self.build_interpretation_block(name, extractor)

        return block, sorted(extractor.worlds)

    def build_interpretation_block(self, name: str, extractor: TPTPModalExtractor) -> str:
            """Pretty-print a single interpretation-worlds block with expansions."""
            # Use the name found in the file, or the passed-in name as fallback
            block_name = extractor.interpretation_worlds_name if extractor.interpretation_worlds_name else name
            
            # worlds: keep original identifiers, deterministically ordered
            worlds = sorted(extractor.worlds)

            # (1) Enumerate worlds in a single disjunction
            enum_line = None
            if worlds:
                disj = " | ".join([f"W = {w}" for w in worlds])
                enum_line = f"! [W: $world] : ( {disj} )"

            # (2) $local_world line if known
            local_line = None
            if extractor.local_world:
                local_line = f"$local_world = {extractor.local_world}"

            # (3) Accessibility lines
            edges_set: Set[Tuple[str, str]] = set()

            # 3a: universal schema present
            if extractor.universal_accessibility and worlds:
                edges_set.update(self.expand_accessibility(worlds))

            # 3b: explicit edges
            for u, vs in extractor.accessible_worlds.items():
                for v in vs:
                    edges_set.add((u, v))

            acc_lines = [f"$accessible_world({u},{v})" for (u, v) in sorted(edges_set)]

            # (4) Assemble with indentation
            body_parts = []
            if enum_line:
                body_parts.append(enum_line)
            
            # --- NEW: Add extra conjuncts (like $distinct) ---
            if extractor.extra_conjuncts:
                body_parts.extend(sorted(extractor.extra_conjuncts))

            if local_line:
                body_parts.append(local_line)
                
            body_parts.extend(acc_lines)

            if not body_parts:
                body = ""
            else:
                body = "\n    & ".join(body_parts)

            return (
                f"tff({block_name},interpretation-worlds,\n"
                f"    ( {body}\n"
                f"    ) )."
            )
    
    def __init__(self):
        pass

    def expand_accessibility(self, worlds: List[str]) -> List[Tuple[str, str]]:
       """Expand ![W,V] : $accessible_world(W,V) into all (world, world) pairs."""
       clauses: List[Tuple[str, str]] = []
       for i in worlds:
           for j in worlds:
               clauses.append((i, j))
       return clauses
    
    def infer_name(self, declarations: List[str]) -> str:
        """Infer the model name from type declarations."""
        for decl in declarations:
            # Look for base type declarations
            if "$tType" in decl and "type," in decl:
                # Extract the type name (simplified - could use more parsing)
                parts = decl.split("type,")
                if len(parts) > 1:
                    type_part = parts[1].split(":")[0].strip()
                    if type_part and not type_part.startswith("d_"):
                        return "model"
        return "model"
    
    def normalize_clause(self, text: str) -> str:
        """Normalize a clause by ensuring it's wrapped in parentheses."""
        text = text.strip()
        if text.endswith("."):
            text = text[:-1].strip()
        if text.startswith("(") and text.endswith(")"):
            return text
        return f"( {text} )"
    
    def world_to_iiv_format(self, world_content: List[str], declarations: str) -> str:
        """Convert world interpretation to IIV format."""
        if not world_content:
            return declarations
        
        # Join and normalize the content blocks
        clauses = [self.normalize_clause(block) for block in world_content if block.strip()]
        
        # Get name from declarations
        name = self.infer_name(declarations.split('\n'))
        
        # Build interpretation
        if clauses:
            joined = "\n  & ".join(clauses)
            interp = f"tff({name},interpretation,\n  ( {joined} ) )."
        else:
            interp = ""
        
        # Combine with declarations
        result = declarations.rstrip()
        if interp:
            result += f"\n\n{interp}\n"
        
        return result
    
    def process_file(self, filepath: str) -> Tuple[Dict[str, str], str, Dict[str, List[str]]]:
        # read file
        input_stream = FileStream(filepath, encoding="utf-8")
        
        # create lexer and parser
        lexer = TPTPLexer(input_stream)
        stream = CommonTokenStream(lexer)
        parser = TPTPParser(stream)
        
        # parse the file
        tree = parser.tptp_file()
        
        walker = ParseTreeWalker()
        extractor = TPTPModalExtractor()
        walker.walk(extractor, tree)
        
        # combine declarations
        declarations = "\n".join(extractor.declarations)
        
        # Convert each world to IIV format to be sent to TSTP endpoint
        results = {}
        for world in extractor.worlds:
            if world in extractor.in_world_blocks:
                content = extractor.in_world_blocks[world]
                converted = self.world_to_iiv_format(content, declarations)
                results[world] = converted
        
        return results, declarations, extractor.accessible_worlds


def main():
    parser = argparse.ArgumentParser(
        description='Parse TPTP modal logic files and extract Tarskian interpretations using ANTLR.'
    )
    parser.add_argument('file', help='Input TPTP file (.s extension)')
    parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # Create parser instance
    tptp_parser = TPTPModalParserANTLR()
    
    try:
        block, worlds = tptp_parser.process_file_new(args.file)

        print("=" * 60)
        print("INTERPRETATION-WORLDS (expanded)")
        print("=" * 60)
        print(f"{block}") # Removed "block is : "
        print()
        print("Worlds:", ", ".join(worlds))


        world_interpretations, declarations, accessibility = tptp_parser.process_file(args.file)
        
        print(f"\nProcessing file: {args.file}")
        print(f"Found {len(world_interpretations)} worlds with interpretations")
        print()
        
        # Print declarations if verbose
        if args.verbose:
            print("=" * 60)
            print("DECLARATIONS:")
            print("=" * 60)
            print(declarations)
            print()
        
        # Print accessibility relations
        if accessibility:
            print("=" * 60)
            print("ACCESSIBILITY RELATIONS:")
            print("=" * 60)
            for from_world, to_worlds in accessibility.items():
                print(f"  {from_world} -> {', '.join(to_worlds)}")
            print()
        
        # Print each world's interpretation
        print("=" * 60)
        print("WORLD INTERPRETATIONS:")
        print("=" * 60)
        
        for world, interpretation in sorted(world_interpretations.items()):
            print(f"\nWorld: {world}")
            print("-" * 40)
            print(interpretation)
            print()
            
            print(f"[send world {world} interpretation to TSTP]")
            print()
    
    except FileNotFoundError:
        print(f"Error: File '{args.file}' not found.", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error processing file: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
