from antlr4.tree.Trees import Trees
from TPTPListener import TPTPListener
from TPTPLexer import TPTPLexer
from TPTPParser import TPTPParser


def parse_text(text: str):
    """Lex, parse, and return (parser, parse_tree)."""
    input_stream = InputStream(text)
    lexer = TPTPLexer(input_stream)
    tokens = CommonTokenStream(lexer)
    parser = TPTPParser(tokens)
    # call the start rule dynamically so you can change START_RULE easily
    if not hasattr(parser, START_RULE):
        raise AttributeError(f"Parser has no rule '{START_RULE}'. "
                             f"Available: {', '.join(parser.ruleNames)}")
    tree = getattr(parser, START_RULE)()
    return parser, tree

def pretty_tree(node, rule_names, indent="", last=True):
    connector = "└── " if last else "├── "
    if hasattr(node, "getChildCount") and node.getChildCount() > 0:
        text = Trees.getNodeText(node, rule_names)
    else:
        text = str(node)  # token/terminal text
    print(indent + connector + text)

    child_count = node.getChildCount() if hasattr(node, "getChildCount") else 0
    for i in range(child_count):
        child = node.getChild(i)
        is_last = (i == child_count - 1)
        pretty_tree(child, rule_names, indent + ("    " if last else "│   "), is_last)

# usage
#
import sys
stdinContent = sys.stdin.read()
parser, tree = parse_text(stdinContent)
pretty_tree(tree, parser.ruleNames)
