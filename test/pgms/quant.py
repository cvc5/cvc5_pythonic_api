from cvc5_pythonic_api import *

f = Function('f', IntSort(), IntSort(), IntSort())
x = Int('x')
y = Int('y')
print(ForAll([x, y], f(x, y) >= x))
