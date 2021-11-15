from cvc5_z3py_compat import *
#from z3 import *
x = Int('x')
y = Int('y')
f = Function('f', IntSort(), IntSort())
solve(f(f(x)) == x, f(x) == y, x != y)
A = DeclareSort('A')
a = Const('a', A)
b = Const('b', A)
solve(a == b)
