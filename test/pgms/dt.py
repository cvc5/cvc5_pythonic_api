from cvc5_pythonic_api import *

TreeList = Datatype('TreeList')
Tree     = Datatype('Tree')
# Tree has two constructors: leaf and node
Tree.declare('leaf', ('val', IntSort()))
# a node contains a list of trees
Tree.declare('node', ('children', TreeList))
TreeList.declare('nil')
TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))
Tree, TreeList = CreateDatatypes(Tree, TreeList)
print(Tree.val(Tree.leaf(10)))
print(simplify(Tree.val(Tree.leaf(10))))
l1 = TreeList.cons(Tree.leaf(20), TreeList.nil)
print(l1)
