import sys, re
from pathlib import Path

TYPE_LINE_RE = re.compile(r'^\s*tff\([^)]*,\s*type\s*,', re.IGNORECASE)
BASE_TYPE_RE = re.compile(
    r'^\s*tff\(\s*([A-Za-z0-9_]+)_type\s*,\s*type\s*,\s*([A-Za-z0-9_]+)\s*:\s*\$tType\s*\)\.\s*$',
    re.IGNORECASE
)
SPLIT_RE = re.compile(r'\)\s*\.\s*(?=\()', re.MULTILINE)

def infer_name(lines):
    for line in lines:
        m = BASE_TYPE_RE.match(line)
        if m:
            return m.group(2)  # e.g., "fruit"
    return "model"

def normalize_clause(text):
    t = text.strip()
    t = re.sub(r'\.\s*$', '', t)  # drop trailing period
    if t.startswith('(') and t.endswith(')'):
        return t
    return f"( {t} )"

def convert_tptp(raw: str) -> str:
    lines = raw.splitlines()
    type_lines = [ln for ln in lines if TYPE_LINE_RE.search(ln)]
    free_lines = [ln for ln in lines if not TYPE_LINE_RE.search(ln)]
    free_text = "\n".join(free_lines).strip()

    # If already has an interpretation block, pass through unchanged
    if re.search(r'tff\s*\(\s*[^,]+,\s*interpretation\s*,', free_text, re.IGNORECASE):
        return raw

    # Split into logical blocks
    blocks = []
    chunks = [c for c in re.split(r'\n\s*\n', free_text) if c.strip()]
    if len(chunks) > 1:
        for ch in chunks:
            blocks.extend([b for b in SPLIT_RE.split(ch) if b.strip()])
    else:
        blocks = [b for b in SPLIT_RE.split(free_text) if b.strip()]
    if not blocks and free_text:
        blocks = [free_text]

    clauses = [normalize_clause(b) for b in blocks] if blocks else []
    name = infer_name(type_lines)

    joined = "\n  & ".join(clauses) if clauses else ""
    interp = f"tff({name},interpretation,\n  ( {joined} ) )." if joined else ""

    body = "\n".join(type_lines).rstrip()
    if interp:
        return f"{body}\n\n{interp}\n"
    else:
        return f"{body}\n"

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 world_to_IIV.py <inputfile> <outputfile>", file=sys.stderr)
        sys.exit(1)

    in_path = Path(sys.argv[1])
    out_path = Path(sys.argv[2])

    try:
        raw = in_path.read_text(encoding="utf-8")
    except Exception as e:
        print(f"Error reading {in_path}: {e}", file=sys.stderr)
        sys.exit(2)

    out_text = convert_tptp(raw)

    try:
        out_path.write_text(out_text, encoding="utf-8")
    except Exception as e:
        print(f"Error writing {out_path}: {e}", file=sys.stderr)
        sys.exit(3)

    # Print to stdout as well
    sys.stdout.write(out_text)

if __name__ == "__main__":
    main()
