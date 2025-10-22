import sys
from antlr4 import *
from TPTPLexer import TPTPLexer
from TPTPParser import TPTPParser
from antlr4.tree.Trees import Trees
from TPTPVisitor import TPTPVisitor
#from antlr4 import ParseTreeWalker
from TPTPListener import TPTPListener



# Create a new listener for finding formulas of type '$world'


class TFFVisitor(TPTPVisitor):
    def visitTff_annotated(sefl,ctx):
        return ctx

def parse_tff(text):
    input_stream = InputStream(Text)
    lexer = TPTPLexer()
    token_stream = CommonTokenStream(lexer)
    parser = TPTPParser(token_stream)

    tree = parser.tff_annotated()
    visitor = TFFVisitor()
    result = visitor.visit(tree)

    return result

class WorldFinderListener(TPTPListener):
    def __init__(self):
        self.world_type_declarations = []

    # This method is called when the walker enters a `tff_atom_typing` rule.
    def enterTff_atom_typing(self, ctx: TPTPParser.Tff_atom_typingContext):
        # The tff_atom_typing rule is structured as:
        # untyped_atom ':' tff_top_level_type
        # We need to check the text of the tff_top_level_type child.
        
        # Access the third child, which is the tff_top_level_type context.
        top_level_type_node = ctx.getChild(2)
        print('ctx.tff_formula:')
        print(ctx.tff_formula().getText())

        # Check the text of the nested node to see if it's '$world'.
        if top_level_type_node and top_level_type_node.getText() == '$world':
            # The name of the formula is two levels above the current context.
            # We can traverse up the tree to find it.
            # tff_atom_typing -> tff_formula -> tff_annotated
            
            # The parent of the current node is `tff_formula`.
            tff_formula_parent = ctx.parentCtx
            # The parent of that is `tff_annotated`.
            tff_annotated_parent = tff_formula_parent.parentCtx
            
            # The first child (index 0) of the tff_annotated context is the formula name.
            formula_name = tff_annotated_parent.getChild(1).getText()
            self.world_type_declarations.append(formula_name)


class PrettyPrintListener(TPTPListener):
    def __init__(self):
        self.level = 0

    def enterEveryRule(self, ctx):
        rule_name = TPTPParser.ruleNames[ctx.getRuleIndex()]
        print("  " * self.level + f"→ {rule_name} | {ctx.getText()}")
        self.level += 1

    def exitEveryRule(self, ctx):
        self.level -= 1

class tffListener(TPTPListener):
    def __init__(self):
        self.level = 0

'''
def main(argv):
    print(TPTPParser.ruleNames)
    # Load input file
    if len(sys.argv) < 1:
        print("usage python3 pp.py [filename]")

    input_stream = FileStream(argv[1], encoding="utf-8")
    
    # Lexer and parser
    lexer = TPTPLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = TPTPParser(stream)
    walker = ParseTreeWalker()
    tree = parser.tptp_file()  
    listener = PrettyPrintListener()
    walker.walk(listener, tree)   
    visitor = TPTPVisitor()
    # entry point (replace 'tptp_file' with the start rule in your grammar)
    
    # Pretty print the parse tree
#    print(Trees.toStringTree(tree, walker, parser))
'''


def main(argv):
    # Load input file
    if len(sys.argv) < 2:
        print("usage: python3 pp.py [filename]")
        return # Use return instead of continuing execution

    input_stream = FileStream(argv[1], encoding="utf-8")
    
    # Lexer and parser
    lexer = TPTPLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = TPTPParser(stream)
    tree = parser.tptp_file()
    
    world_finder = WorldFinderListener()
    walker = ParseTreeWalker()
    walker.walk(world_finder, tree)

    # Access the list by its correct name
    if world_finder.world_type_declarations:
        print("\nFound the following formulas of type '$world':")
        for name in world_finder.world_type_declarations:
            print(f"- {name}")
    else:
        print("\nNo formulas of type '$world' found.")# Create and run your new listener




if __name__ == '__main__':
    main(sys.argv)

if __name__ == '__main__':
    main(sys.argv)
