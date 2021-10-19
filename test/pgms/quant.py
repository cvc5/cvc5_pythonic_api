from cvc5_z3py_compat import *
f = Function('f', IntSort(), IntSort(), IntSort())
x = Int('x')
y = Int('y')
print(ForAll([x, y], f(x, y) >= x))
