#!/usr/bin/env python3

import sys
import os
import re
from typing import Dict, List, Set, Tuple, Optional
import argparse
from antlr4 import *

from TPTPLexer import TPTPLexer
from TPTPParser import TPTPParser
from TPTPVisitor import TPTPVisitor


class TPTPModalExtractorVisitor(TPTPVisitor):
    """
    Visitor-based extractor.  Replaces the Listener version to enable
    selective subtree traversal and an O(1) scope-stack lookup instead
    of the O(depth) parent-chain walk used previously.

    Key optimisations over the Listener version:
      1. `visitTff_annotated` skips every block whose role is not 'type'
         or 'interpretation-worlds' — the vast majority of tff() blocks
         in a large file are never descended into.
      2. `visitTff_quantified_formula` maintains a scope stack so that
         is_universally_quantified_world() is an O(stack-depth) dict
         lookup rather than an O(tree-depth) parent-pointer walk.
      3. `visitTff_prefix_unary` maintains a negation counter, removing
         the second parent-pointer walk for polarity detection.
      4. No nested ParseTreeWalker — extra_conjuncts are collected in the
         same pass via the _in_interp_worlds flag.
      5. All try/except attribute chains replaced by getText() +
         uppercase-initial check (TPTP spec: variables start uppercase).
    """

    def __init__(self):
        self.worlds: Set[str] = set()
        self.accessible_worlds: Dict[str, List[str]] = {}
        self.universal_accessibility: bool = False
        self.universal_polarity: bool = True
        self.local_world: Optional[str] = None
        self.extra_conjuncts: List[str] = []
        self.interpretation_worlds_name: str = "model_worlds"

        # Quantifier scope stack.
        # Each frame: {'_q': '!' | '?', var_name: type_str, ...}
        self._scope: List[Dict[str, Optional[str]]] = []
        # Net negation depth at the current tree position (odd = negated).
        self._negation_depth: int = 0
        # True only while inside an interpretation-worlds block.
        self._in_interp_worlds: bool = False

    def _parse_variable_list(self, var_list_ctx) -> Dict[str, Optional[str]]:
        """Walk the right-recursive tff_variable_list, returning {name: type}."""
        bindings: Dict[str, Optional[str]] = {}
        current = var_list_ctx
        while current is not None:
            var_ctx = (current.tff_variable()
                       if hasattr(current, 'tff_variable') else None)
            if var_ctx:
                typed = (var_ctx.tff_typed_variable()
                         if hasattr(var_ctx, 'tff_typed_variable') else None)
                if typed and typed.variable() and typed.tff_atomic_type():
                    bindings[typed.variable().getText()] = typed.tff_atomic_type().getText()
                elif var_ctx.variable():
                    bindings[var_ctx.variable().getText()] = None
            current = (current.tff_variable_list()
                       if hasattr(current, 'tff_variable_list') else None)
        return bindings

    def _is_universally_quantified_world(self, var_name: str) -> bool:
        """O(scope-depth) lookup — replaces O(tree-depth) parent-chain walk."""
        return any(
            frame.get('_q') == '!' and frame.get(var_name) == '$world'
            for frame in self._scope
        )

    def _get_argument_texts(self, args_ctx) -> List[str]:
        """Flatten tff_arguments into a list of raw getText() strings."""
        texts: List[str] = []
        if args_ctx.tff_term():
            texts.append(args_ctx.tff_term().getText())
        comma_terms = args_ctx.comma_tff_term()
        if comma_terms:
            if isinstance(comma_terms, list):
                for ct in comma_terms:
                    if ct.tff_term():
                        texts.append(ct.tff_term().getText())
            else:
                if comma_terms.tff_term():
                    texts.append(comma_terms.tff_term().getText())
        return texts

    @staticmethod
    def _is_variable_name(name: str) -> bool:
        """TPTP variables must start with an uppercase letter (section 2.1)."""
        return bool(name) and name[0].isupper()

    def visitTff_annotated(self, ctx: TPTPParser.Tff_annotatedContext):
        role = ctx.formula_role().getText() if ctx.formula_role() else None

        if role == 'interpretation-worlds':
            if ctx.name():
                self.interpretation_worlds_name = ctx.name().getText()
            self._in_interp_worlds = True
            self.visitChildren(ctx)
            self._in_interp_worlds = False
            return

        # Only the interpretation-worlds block is passed to ANTLR, so any
        # other role here is unexpected — skip it.

    def visitTff_quantified_formula(self, ctx: TPTPParser.Tff_quantified_formulaContext):
        q_text = ctx.tff_quantifier().getText() if ctx.tff_quantifier() else None
        var_list = ctx.tff_variable_list()
        bindings = self._parse_variable_list(var_list) if var_list else {}
        self._scope.append({'_q': q_text, **bindings})
        self.visitChildren(ctx)
        self._scope.pop()

    def visitTff_prefix_unary(self, ctx: TPTPParser.Tff_prefix_unaryContext):
        is_neg = (ctx.tff_unary_connective()
                  and ctx.tff_unary_connective().getText() == '~')
        if is_neg:
            self._negation_depth += 1
        self.visitChildren(ctx)
        if is_neg:
            self._negation_depth -= 1

    # $local_world detection

    def visitTff_defined_infix(self, ctx: TPTPParser.Tff_defined_infixContext):
        pred = ctx.defined_infix_pred()
        if pred and pred.infix_equality():
            lhs = ctx.tff_unitary_term(0).getText()
            rhs = ctx.tff_unitary_term(1).getText()
            if lhs == '$local_world':
                self.local_world = rhs
                self.worlds.add(rhs)
            elif rhs == '$local_world':
                self.local_world = lhs
                self.worlds.add(lhs)
            elif self._in_interp_worlds:
                # Capture world names from the enum line:
                #   ! [W: $world] : (W = world_0 | W = world_1 | ...)
                # One side is a universally-quantified world variable, the
                # other is a constant — that constant is a world name.
                if (self._is_variable_name(lhs)
                        and self._is_universally_quantified_world(lhs)
                        and not self._is_variable_name(rhs)):
                    self.worlds.add(rhs)
                elif (self._is_variable_name(rhs)
                      and self._is_universally_quantified_world(rhs)
                      and not self._is_variable_name(lhs)):
                    self.worlds.add(lhs)
        # infix formula is a leaf for our purposes — no visitChildren

    # $accessible_world edges and extra conjunct collection

    def visitTff_defined_plain(self, ctx: TPTPParser.Tff_defined_plainContext):
        if not ctx.defined_functor():
            self.visitChildren(ctx)
            return

        func_name = ctx.defined_functor().getText()

        if func_name == '$accessible_world' and ctx.tff_arguments():
            terms = self._get_argument_texts(ctx.tff_arguments())
            if len(terms) >= 2:
                w1, w2 = terms[0], terms[1]
                if (self._is_variable_name(w1) and self._is_variable_name(w2)
                        and self._is_universally_quantified_world(w1)
                        and self._is_universally_quantified_world(w2)):
                    # Universal quantification over both world args
                    self.universal_accessibility = True
                    self.universal_polarity = (self._negation_depth % 2 == 0)
                elif (not self._is_variable_name(w1)
                      and not self._is_variable_name(w2)):
                    # Concrete edge
                    self.worlds.update([w1, w2])
                    self.accessible_worlds.setdefault(w1, []).append(w2)
            return  # $accessible_world is always a leaf

        if self._in_interp_worlds and func_name.startswith('$'):
            text = ctx.getText()
            if '$local_world' not in text:
                self.extra_conjuncts.append(text)
            return  # captured as a whole conjunct; don't descend

        self.visitChildren(ctx)


class TPTPInWorldExpanderVisitor(TPTPVisitor):
    """
    Detects ! [W: $world] : $in_world(W, BODY) at the top level of an
    interpretation-domains or interpretation-mappings block and records
    the world variable name and original-source body text.

    Only the outermost universal world quantifier triggers expansion —
    inner FOL quantifiers (! [C: child], etc.) inside BODY are left
    untouched because visitTff_defined_plain captures BODY as raw text
    without descending into it.
    """

    def __init__(self, source_text: str):
        self._source: str = source_text
        self.world_var: Optional[str] = None
        self.body_text: Optional[str] = None
        self._in_target_block: bool = False
        self._found_outer_quantifier: bool = False

    def _parse_variable_list(self, var_list_ctx) -> Dict[str, Optional[str]]:
        bindings: Dict[str, Optional[str]] = {}
        current = var_list_ctx
        while current is not None:
            var_ctx = (current.tff_variable()
                       if hasattr(current, 'tff_variable') else None)
            if var_ctx:
                typed = (var_ctx.tff_typed_variable()
                         if hasattr(var_ctx, 'tff_typed_variable') else None)
                if typed and typed.variable() and typed.tff_atomic_type():
                    bindings[typed.variable().getText()] = typed.tff_atomic_type().getText()
                elif var_ctx.variable():
                    bindings[var_ctx.variable().getText()] = None
            current = (current.tff_variable_list()
                       if hasattr(current, 'tff_variable_list') else None)
        return bindings

    def visitTff_annotated(self, ctx: TPTPParser.Tff_annotatedContext):
        role = ctx.formula_role().getText() if ctx.formula_role() else None
        if role in ('interpretation-domains', 'interpretation-mappings'):
            self._in_target_block = True
            self.visitChildren(ctx)
            self._in_target_block = False

    def visitTff_quantified_formula(self, ctx: TPTPParser.Tff_quantified_formulaContext):
        if not self._in_target_block:
            return
        if self._found_outer_quantifier:
            # Inner quantifier inside BODY — do not recurse; leave it as-is.
            return

        q_text = ctx.tff_quantifier().getText() if ctx.tff_quantifier() else None
        if q_text != '!':
            return

        var_list = ctx.tff_variable_list()
        bindings = self._parse_variable_list(var_list) if var_list else {}
        world_vars = [name for name, typ in bindings.items() if typ == '$world']
        if len(world_vars) != 1:
            return

        self._found_outer_quantifier = True
        self.world_var = world_vars[0]
        self.visitChildren(ctx)

    def visitTff_defined_plain(self, ctx: TPTPParser.Tff_defined_plainContext):
        if not self._found_outer_quantifier or self.body_text is not None:
            return
        if not ctx.defined_functor():
            return

        func_name = ctx.defined_functor().getText()
        if func_name != '$in_world' or not ctx.tff_arguments():
            return

        args = ctx.tff_arguments()
        first_term = args.tff_term()
        if first_term is None or first_term.getText() != self.world_var:
            return

        comma_terms = args.comma_tff_term()
        if not comma_terms:
            return
        ct = comma_terms[0] if isinstance(comma_terms, list) else comma_terms
        body_ctx = ct.tff_term()
        if body_ctx is None:
            return

        # WS is skipped by the lexer, but token.start / token.stop are character
        # offsets into the original InputStream — slicing the source preserves
        # all whitespace and internal indentation verbatim.
        self.body_text = self._source[body_ctx.start.start: body_ctx.stop.stop + 1]
        # Do NOT call visitChildren — BODY is fully captured as source text.


# --------------------------------------------------------------------------- #

class TPTPModalParserANTLR:

    def __init__(self):
        self.block_regex = re.compile(
            r"tff\(([^,]+)\s*,\s*interpretation-worlds\s*,\s*(.*?)\)\s*\.\s*$",
            re.MULTILINE | re.DOTALL
        )
        self.domains_regex = re.compile(
            r"tff\(([^,]+)\s*,\s*interpretation-domains\s*,\s*(.*?)\)\s*\.\s*$",
            re.MULTILINE | re.DOTALL
        )
        self.mappings_regex = re.compile(
            r"tff\(([^,]+)\s*,\s*interpretation-mappings\s*,\s*(.*?)\)\s*\.\s*$",
            re.MULTILINE | re.DOTALL
        )

    def run_extractor(self, raw_text: str) -> TPTPModalExtractorVisitor:
        # Parse only the interpretation-worlds block — typically 20-50 lines
        # vs. hundreds or thousands in the full file.  World names are
        # discovered from the enum formula and concrete edges inside the block
        # itself, so no type-declaration blocks are needed.
        iw_match = self.block_regex.search(raw_text)
        mini_text = (iw_match.group(0) if iw_match else '') + '\n'
        input_stream = InputStream(mini_text)
        lexer = TPTPLexer(input_stream)
        stream = CommonTokenStream(lexer)
        parser = TPTPParser(stream)
        tree = parser.tptp_file()
        extractor = TPTPModalExtractorVisitor()
        extractor.visit(tree)
        return extractor

    def _run_inworld_expander(self, block_text: str) -> TPTPInWorldExpanderVisitor:
        input_stream = InputStream(block_text)
        lexer = TPTPLexer(input_stream)
        stream = CommonTokenStream(lexer)
        parser = TPTPParser(stream)
        tree = parser.tptp_file()
        expander = TPTPInWorldExpanderVisitor(block_text)
        expander.visit(tree)
        return expander

    def _build_inworld_block(
        self, block_name: str, block_role: str, body_text: str, worlds: List[str]
    ) -> str:
        parts = [f"$in_world({w},\n        {body_text})" for w in worlds]
        joined = "\n    & ".join(parts)
        return f"tff({block_name},{block_role},\n    ( {joined} ) )."

    def get_expanded_file_content(self, filepath: str) -> Optional[str]:
        with open(filepath, 'r', encoding='utf-8') as f:
            raw_text = f.read()

        # Early exit: if no interpretation-worlds block, nothing to expand.
        if not self.block_regex.search(raw_text):
            return raw_text

        extractor = self.run_extractor(raw_text)
        worlds = sorted(extractor.worlds)
        new_expanded_block = self.build_interpretation_block(extractor)
        result = self.block_regex.sub(new_expanded_block, raw_text, count=1)

        for role_regex, role_name in (
            (self.domains_regex, 'interpretation-domains'),
            (self.mappings_regex, 'interpretation-mappings'),
        ):
            def replacer(m, role_name=role_name, worlds=worlds):
                block_text = m.group(0)
                block_name = m.group(1).strip()
                expander = self._run_inworld_expander(block_text)
                if expander.world_var is None or expander.body_text is None:
                    return block_text
                return self._build_inworld_block(block_name, role_name, expander.body_text, worlds)
            result = role_regex.sub(replacer, result, count=1)

        return result

    def build_interpretation_block(self, extractor: TPTPModalExtractorVisitor) -> str:
        block_name = extractor.interpretation_worlds_name
        worlds = sorted(extractor.worlds)

        enum_line = None
        if worlds:
            disj = " | ".join([f"W = {w}" for w in worlds])
            enum_line = f"! [W: $world] : ( {disj} )"

        local_line = None
        if extractor.local_world:
            local_line = f"$local_world = {extractor.local_world}"

        acc_lines: List[str] = []

        if extractor.universal_accessibility and worlds:
            for u in worlds:
                for v in worlds:
                    if extractor.universal_polarity:
                        acc_lines.append(f"$accessible_world({u},{v})")
                    else:
                        acc_lines.append(f"~ $accessible_world({u},{v})")

        edges_set: Set[Tuple[str, str]] = set()
        for u, vs in extractor.accessible_worlds.items():
            for v in vs:
                edges_set.add((u, v))
        for (u, v) in sorted(edges_set):
            acc_lines.append(f"$accessible_world({u},{v})")

        acc_lines.sort()

        body_parts: List[str] = []
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


def make_html_friendly(file_text: str) -> str:
    return file_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def main():
    parser = argparse.ArgumentParser(
        description='Expands universal accessibility in TPTP modal logic files.'
    )
    parser.add_argument('file', help='Input TPTP file (.p or .tptp extension)')
    parser.add_argument('--output', default="/dev/null", help='Output filepath')
    parser.add_argument('--html', type=int, default=0, help="1 for html sanitization, 0 for plain")
    parser.add_argument('--stdout', type=int, default=1, help="1 for printing to stdout, 0 for no printing")

    args = parser.parse_args()

    tptp_parser = TPTPModalParserANTLR()

    try:
        expanded_content = tptp_parser.get_expanded_file_content(args.file)

        if expanded_content is None:
            print(f"Error: Could not find 'interpretation-worlds' block in {args.file}", file=sys.stderr)
            sys.exit(1)

        if args.html == 1:
            final_output = make_html_friendly(expanded_content)
        else:
            final_output = expanded_content

        if os.path.isdir(args.output):
            base_name = os.path.basename(args.file)
            name_without_ext, ext = os.path.splitext(base_name)
            out_dir = os.path.abspath(args.output)
            new_filename = os.path.join(out_dir, f"{name_without_ext}_EXPANDED.s")
        else:
            new_filename = args.output
            # Only try to create directories if writing to a real path instead of /dev/null
            if new_filename != "/dev/null":
                os.makedirs(os.path.dirname(os.path.abspath(new_filename)), exist_ok=True)

        with open(new_filename, 'w', encoding='utf-8') as f:
            f.write(final_output)

        print("% SZS status Success")
        if args.stdout == 1:
            print(final_output)

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
