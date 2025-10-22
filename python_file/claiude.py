#!/usr/bin/env python3
"""
TPTP Modal Logic World Parser
Extracts Tarskian interpretations from modal logic TPTP files with multiple worlds.
"""

import re
import sys
from typing import Dict, List, Set, Tuple
import argparse


class TPTPModalParser:
    """Parser for TPTP modal logic files with multiple worlds."""
    
    def __init__(self):
        # Regex patterns
        self.TYPE_LINE_RE = re.compile(r'^\s*tff\([^)]*,\s*type\s*,', re.IGNORECASE)
        self.BASE_TYPE_RE = re.compile(
            r'^\s*tff\(\s*([A-Za-z0-9_]+)_type\s*,\s*type\s*,\s*([A-Za-z0-9_]+)\s*:\s*\$tType\s*\)\.\s*$',
            re.IGNORECASE
        )
        self.WORLD_DECL_RE = re.compile(
            r'^\s*tff\([^,]+,\s*type\s*,\s*([A-Za-z_]\w*)\s*:\s*\$world\s*\)\s*\.\s*$',
            re.IGNORECASE | re.MULTILINE
        )
        self.ACCESSIBLE_WORLD_RE = re.compile(r'\$accessible_world\((\w+),\s*(\w+)\)')
        
    def parse_declarations(self, text: str) -> str:
        """Extract type declarations from the input text."""
        lines = text.split('\n')
        out = []
        started = False
        
        for line in lines:
            if self.TYPE_LINE_RE.match(line):
                started = True
                out.append(line)
                continue
            
            if not started:
                if line.strip() == "":
                    continue
                else:
                    continue
            
            # We have started collecting declarations
            if line.strip() == "":
                out.append(line)
                continue
            
            # First non-blank, non-declaration after we've started → stop
            break
        
        return '\n'.join(out)
    
    def parse_worlds(self, text: str) -> List[str]:
        """Extract declared world names from the text."""
        worlds = set()
        for match in self.WORLD_DECL_RE.finditer(text):
            worlds.add(match.group(1))
        return sorted(list(worlds))
    
    def parse_in_world_blocks(self, text: str) -> Dict[str, str]:
        """Parse $in_world blocks and organize content by world."""
        # Get declared worlds
        worlds = self.parse_worlds(text)
        world_set = set(worlds)
        
        # Initialize dictionary for world content
        world_dict = {w: "" for w in worlds}
        
        # Find all $in_world occurrences
        target = "$in_world("
        idx = text.find(target)
        
        while idx != -1:
            start_arg = idx + len(target)
            
            # Parse first argument (world name)
            i = start_arg
            while i < len(text) and text[i].isspace():
                i += 1
            arg_start = i
            
            # Read identifier
            while i < len(text) and (text[i].isalnum() or text[i] == '_'):
                i += 1
            first_arg = text[arg_start:i]
            
            # Skip to comma
            while i < len(text) and text[i].isspace():
                i += 1
            if i >= len(text) or text[i] != ',':
                idx = text.find(target, idx + 1)
                continue
            
            comma_idx = i
            
            # Parse matching parentheses to get the body
            depth = 1  # We're inside $in_world(...)
            i = comma_idx + 1
            while i < len(text) and depth > 0:
                if text[i] == '(':
                    depth += 1
                elif text[i] == ')':
                    depth -= 1
                i += 1
            
            # Extract body
            body = text[comma_idx + 1:i - 1].strip()
            
            # Add to appropriate world(s)
            if first_arg in world_set:
                # Concrete world name
                if world_dict[first_arg]:
                    world_dict[first_arg] += "\n"
                world_dict[first_arg] += body
            else:
                # Check if it's a universally quantified variable
                lookback = text[max(0, idx - 400):idx]
                q_match = re.search(r'!\s*\[\s*([A-Za-z_]\w*)\s*:\s*\$world\s*\]\s*:', lookback)
                
                if q_match and q_match.group(1) == first_arg:
                    # Add to all worlds
                    for w in worlds:
                        if world_dict[w]:
                            world_dict[w] += "\n"
                        world_dict[w] += body
            
            # Find next occurrence
            idx = text.find(target, i)
        
        return world_dict
    
    def infer_name(self, lines: List[str]) -> str:
        """Infer the model name from type declarations."""
        for line in lines:
            match = self.BASE_TYPE_RE.match(line)
            if match:
                return match.group(2)
        return "model"
    
    def normalize_clause(self, text: str) -> str:
        """Normalize a clause by ensuring it's wrapped in parentheses."""
        text = text.strip()
        text = re.sub(r'\.\s*$', '', text)
        if text.startswith('(') and text.endswith(')'):
            return text
        return f"( {text} )"
    
    def split_top_level_clauses(self, s: str) -> List[str]:
        """Split a string into clauses at top-level parenthesis boundaries."""
        parts = []
        buf = ""
        depth = 0
        
        for i, ch in enumerate(s):
            buf += ch
            
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth = max(0, depth - 1)
            
            # When we close a top-level group, check for next '('
            if depth == 0 and ch == ')':
                j = i + 1
                while j < len(s) and s[j].isspace():
                    j += 1
                if j < len(s) and s[j] == '(':
                    parts.append(buf.strip())
                    buf = ""
        
        if buf.strip():
            parts.append(buf.strip())
        
        return parts if parts else [s]
    
    def world_to_iiv_format(self, raw_text: str, declarations: str = "") -> str:
        """Convert world interpretation to IIV format."""
        lines = raw_text.split('\n')
        type_lines = [ln for ln in lines if self.TYPE_LINE_RE.match(ln)]
        free_lines = [ln for ln in lines if not self.TYPE_LINE_RE.match(ln)]
        free_text = '\n'.join(free_lines).strip()
        
        # Check if already in interpretation format
        if re.search(r'\btff\s*\(\s*[^,]+,\s*interpretation\s*,', free_text, re.IGNORECASE):
            return raw_text
        
        # Split into blocks
        blocks = []
        chunks = [c for c in free_text.split('\n\n') if c.strip()]
        
        if len(chunks) > 1:
            for chunk in chunks:
                split_parts = re.split(r'\)\s*\.\s*(?=\()', chunk)
                blocks.extend([b for b in split_parts if b.strip()])
        elif free_text:
            blocks = re.split(r'\)\s*\.\s*(?=\()', free_text)
            blocks = [b for b in blocks if b.strip()]
        
        if not blocks and free_text:
            blocks = [free_text]
        
        # Fallback: split by top-level parenthesis boundaries
        if len(blocks) == 1:
            top_level = self.split_top_level_clauses(blocks[0])
            if len(top_level) > 1:
                blocks = top_level
        
        # Normalize clauses
        clauses = [self.normalize_clause(b) for b in blocks] if blocks else []
        
        # Get name from type lines
        name = self.infer_name(type_lines)
        
        # Build interpretation
        joined = '\n  & '.join(clauses) if clauses else ""
        interp = f"tff({name},interpretation,\n  ( {joined} ) )." if joined else ""
        
        # Combine with declarations if provided
        if declarations:
            return f"{declarations.rstrip()}\n\n{interp}\n" if interp else f"{declarations}\n"
        
        body = '\n'.join(type_lines).rstrip()
        return f"{body}\n\n{interp}\n" if interp else f"{body}\n"
    
    def parse_accessible_worlds(self, text: str) -> Dict[str, List[str]]:
        """Parse accessibility relations between worlds."""
        world_dict = {}
        for match in self.ACCESSIBLE_WORLD_RE.finditer(text):
            from_world, to_world = match.groups()
            if from_world not in world_dict:
                world_dict[from_world] = []
            world_dict[from_world].append(to_world)
        return world_dict
    
    def process_file(self, filepath: str) -> Dict[str, str]:
        """Process a TPTP file and extract world interpretations."""
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Parse declarations
        declarations = self.parse_declarations(content)
        
        # Parse worlds and their content
        world_dict = self.parse_in_world_blocks(content)
        
        # Parse accessibility relations (for reference)
        accessibility = self.parse_accessible_worlds(content)
        
        # Convert each world to IIV format
        results = {}
        for world, content in world_dict.items():
            if content:  # Only process worlds with content
                converted = self.world_to_iiv_format(content, declarations)
                results[world] = converted
        
        return results, declarations, accessibility


def main():
    parser = argparse.ArgumentParser(
        description='Parse TPTP modal logic files and extract Tarskian interpretations for each world.'
    )
    parser.add_argument('file', help='Input TPTP file (.s extension)')
    parser.add_argument('-o', '--output', help='Output directory for world files', default='.')
    parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # Create parser instance
    tptp_parser = TPTPModalParser()
    
    try:
        # Process the file
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
            
            # Note: This is where you would send to TSTP
            # For now, we're just printing as requested
            print(f"[Would send world {world} interpretation to TSTP]")
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
