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
        return hasattr(term_ctx, "variable") and callable(term_ctx.variable) and term_ctx.variable() is not None

    def term_constant_text(self, term_ctx) -> Optional[str]:
        """Return text of a plain constant if present; else None."""
        # Try to follow: term -> (maybe) logic_formula -> unitary -> atomic -> plain_atomic -> constant
        if hasattr(term_ctx, "tff_logic_formula") and callable(term_ctx.tff_logic_formula):
            f = term_ctx.tff_logic_formula()
            if f and hasattr(f, "tff_unitary_formula") and callable(f.tff_unitary_formula):
                u = f.tff_unitary_formula()
                if u and hasattr(u, "tff_atomic_formula"):
                    a = u.tff_atomic_formula()
                    if a and hasattr(a, "tff_plain_atomic"):
                        p = a.tff_plain_atomic()
                        if p and hasattr(p, "constant") and p.constant():
                            return p.constant().getText()
        # Fallback: if not a variable and not a structured term, getText() may still be a constant token
        if not self.term_is_variable(term_ctx):
            return term_ctx.getText()
        return None

    def both_args_universally_quantified_worlds(self, ctx, arg_term_ctxs) -> bool:
        """Return True iff both arguments are variables universally quantified as $world in some ancestor."""
        if len(arg_term_ctxs) < 2:
            return False
        lhs, rhs = arg_term_ctxs[0], arg_term_ctxs[1]
        if not (self.term_is_variable(lhs) and self.term_is_variable(rhs)):
            return False
        vL = lhs.variable().getText()
        vR = rhs.variable().getText()
        return self.is_universally_quantified_world(ctx, vL) and self.is_universally_quantified_world(ctx, vR)
    """Listener to extract modal logic components from TPTP parse tree."""
    
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
            # ANTLR indexable rule children
            lhs = ctx.tff_term(0) if ctx.tff_term(0) else None
            rhs = ctx.tff_term(1) if ctx.tff_term(1) else None
        else:
            lhs = rhs = None

        if not lhs or not rhs:
            return

        lhs_txt = self.get_term_text(lhs)
        rhs_const = self.term_constant_text(rhs)
        lhs_const = self.term_constant_text(lhs)
        rhs_txt = self.get_term_text(rhs)

        # $local_world = <const>
        if lhs_txt == "$local_world" and rhs_const:
            self.local_world = rhs_const
            self.worlds.add(rhs_const)

        # Harvest worlds from equalities with a world-typed variable on one side and a constant on the other
        # (we only add the constant if the other side is a universally quantified $world variable in an ancestor)
        if self.term_is_variable(lhs) and rhs_const:
            v = lhs.variable().getText()
            if self.is_universally_quantified_world(ctx, v):
                self.worlds.add(rhs_const)
        if self.term_is_variable(rhs) and lhs_const:
            v = rhs.variable().getText()
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
                        # could be a universally quantified variable, look for a parent quantification
                        if self.is_universally_quantified_world(ctx, world_arg):
                            # add to all worlds
                            for world in self.worlds:
                                if world not in self.in_world_blocks:
                                    self.in_world_blocks[world] = []
                                self.in_world_blocks[world].append(content)
            
            elif func_name == "$accessible_world" and ctx.tff_arguments():
                #NEW 
                args = ctx.tff_arguments()
                term_ctxs = self.get_argument_term_contexts(args)
                terms_txt = [self.get_term_text(tc) for tc in term_ctxs]

                # Case A: universally quantified schema  ![W,V:$world] : $accessible_world(W,V)
                if self.both_args_universally_quantified_worlds(ctx, term_ctxs):
                    self.universal_accessibility = True
                    # Do NOT add edges now; we’ll expand later with all world pairs
                    return

                # Case B: explicit edge $accessible_world(wi,wj) with constants
                if len(terms_txt) >= 2:
                    from_world_txt = terms_txt[0]
                    to_world_txt = terms_txt[1]

                    # If constants, record edge (variables will be ignored here)
                    if not self.term_is_variable(term_ctxs[0]) and not self.term_is_variable(term_ctxs[1]):
                        if from_world_txt not in self.accessible_worlds:
                            self.accessible_worlds[from_world_txt] = []
                        self.accessible_worlds[from_world_txt].append(to_world_txt)

                        # keep track of any world constants we see
                        self.worlds.add(from_world_txt)
                        self.worlds.add(to_world_txt)

                #OLD
                # get accessibility relation
#                args = ctx.tff_arguments()
#                terms = self.get_argument_terms(args)
#                
#                if len(terms) >= 2:
#                    from_world = terms[0]
#                    to_world = terms[1]
#                    if from_world not in self.accessible_worlds:
#                        self.accessible_worlds[from_world] = []
#                    self.accessible_worlds[from_world].append(to_world)
    
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
        """Extract text from a term context, handling variables and constants."""
        # Try to get the most specific identifier
        if hasattr(term_ctx, 'variable') and callable(term_ctx.variable):
            var_ctx = term_ctx.variable()
            if var_ctx:
                return var_ctx.getText()
        
        if hasattr(term_ctx, 'tff_logic_formula') and callable(term_ctx.tff_logic_formula):
            formula = term_ctx.tff_logic_formula()
            if formula:
                # Check for atomic formula
                if hasattr(formula, 'tff_unitary_formula') and callable(formula.tff_unitary_formula):
                    unitary = formula.tff_unitary_formula()
                    if unitary and hasattr(unitary, 'tff_atomic_formula'):
                        atomic = unitary.tff_atomic_formula()
                        if atomic and hasattr(atomic, 'tff_plain_atomic'):
                            plain = atomic.tff_plain_atomic()
                            if plain and hasattr(plain, 'constant'):
                                const = plain.constant()
                                if const:
                                    return const.getText()
        
        # Fallback to full text
        return term_ctx.getText()
    
    def extract_in_world_content(self, ctx):
        """Extract the content within $in_world(W, ...) - just the ... part."""
        # Navigate to the arguments
        if not ctx.tff_arguments():
            return ""
        
        args = ctx.tff_arguments()
        
        # We need to get everything after the first comma
        # This is the second argument onwards
        comma_terms = args.comma_tff_term()
        if comma_terms:
            if isinstance(comma_terms, list) and comma_terms:
                # Get the text of the first comma_tff_term (which is the content)
                content_ctx = comma_terms[0].tff_term() if comma_terms[0].tff_term() else comma_terms[0]
            else:
                content_ctx = comma_terms.tff_term() if comma_terms.tff_term() else comma_terms
            
            # Get the original text preserving formatting
            return self.get_original_text(content_ctx)
        
        return ""
    
    def is_universally_quantified_world(self, ctx, var_name):
        """Check if a variable is universally quantified as a world in parent context."""
        parent = ctx.parentCtx
        
        # Navigate up the tree looking for quantifiers
        while parent:
            if isinstance(parent, TPTPParser.Tff_quantified_formulaContext):
                # Check if it's universal quantification
                if parent.tff_quantifier() and parent.tff_quantifier().getText() == "!":
                    # Check variable list
                    var_list = parent.tff_variable_list()
                    if var_list:
                        # Check if our variable is declared as $world type
                        variables = self.extract_typed_variables(var_list)
                        for var, var_type in variables:
                            if var == var_name and var_type == "$world":
                                return True
            parent = parent.parentCtx
        
        return False
    
    def extract_typed_variables(self, var_list_ctx):
        """Extract variable names and types from a variable list."""
        variables = []
        
        # Handle single variable
        if var_list_ctx.tff_variable():
            var_ctx = var_list_ctx.tff_variable()
            if var_ctx.tff_typed_variable():
                typed_var = var_ctx.tff_typed_variable()
                if typed_var.variable() and typed_var.tff_atomic_type():
                    var_name = typed_var.variable().getText()
                    var_type = typed_var.tff_atomic_type().getText()
                    variables.append((var_name, var_type))
        
        
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
        name = "model_worlds"  

        block = self.build_interpretation_block(name, extractor)

        return block, sorted(extractor.worlds)

    def build_interpretation_block(self, name: str, extractor: TPTPModalExtractor) -> str:
            """Pretty-print a single interpretation-worlds block with expansions."""
            # worlds: keep original identifiers, deterministically ordered
            worlds = sorted(extractor.worlds)

            # (1) Enumerate worlds in a single disjunction  ![W:$world] : ( W = w1 | W = w2 | ... )
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

            # 3a: universal schema present → full n^2 edges
            if extractor.universal_accessibility and worlds:
                edges_set.update(self.expand_accessibility(worlds))

            # 3b: explicit edges found in the file
            for u, vs in extractor.accessible_worlds.items():
                for v in vs:
                    edges_set.add((u, v))

            acc_lines = [f"$accessible_world({u},{v})" for (u, v) in sorted(edges_set)]

            # (4) Assemble with indentation
            body_parts = []
            if enum_line:
                body_parts.append(enum_line)
            if local_line:
                body_parts.append(local_line)
            body_parts.extend(acc_lines)

            if not body_parts:
                body = ""
            else:
                body = "\n    & ".join(body_parts)

            return (
                f"tff({name},interpretation-worlds,\n"
                f"    ( {body}\n"
                f"    ) )."
            )
    
    def __init__(self):
        pass

    def expand_accessibility(self, worlds: List[str]) -> List[str]:
       """Expand ![W,V] : $accessible_world(W,V) into all pairs."""
       clauses = []
       for i in worlds:
           for j in worlds:
               clauses.append(f"$accessible_world({i},{j})")
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
        print(f"block is : {block}")
        print()
        print("Worlds:", ", ".join(worlds))


        world_interpretations, declarations, accessibility = tptp_parser.process_file(args.file)
        
        print(f"Processing file: {args.file}")
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
