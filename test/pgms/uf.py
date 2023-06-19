from cvc5_pythonic_api import *

x = Int('x')
y = Int('y')
f = Function('f', IntSort(), IntSort())
solve(f(f(x)) == x, f(x) == y, x != y)
A = DeclareSort('A')
a = Const('a', A)
b = Const('b', A)
solve(a == b)
