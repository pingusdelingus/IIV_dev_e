import sys
from antlr4 import *
from TPTPLexer import TPTPLexer
from TPTPParser import TPTPParser

def format_tptp(filename):
    # load input
    input_stream = FileStream(filename, encoding="utf-8")

    # lex and parse
    lexer = TPTPLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = TPTPParser(stream)

    tree = parser.tptp_file()   # adjust start rule

    # get *all* tokens
    stream.fill()
    tokens = stream.tokens

    # filter out whitespace/comments (channel 0 = default)
    cleaned = [tok.text for tok in tokens if tok.channel == 0]
    
    
    # join back into one normalized string
    return "".join(cleaned)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 reformat.py file.tptp")
        sys.exit(1)

    output = format_tptp(sys.argv[1])
    print(output)
