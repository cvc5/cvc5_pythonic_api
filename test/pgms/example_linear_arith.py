from cvc5_z3py_compat import *

slv = SolverFor('QF_LIRA')

x = Int('x')
y = Real('y')

slv.add(And(x >= 3 * y, x <= y, -2 < x))
slv.push()
print(slv.check(y-x <= 2/3))
slv.pop()
slv.push()
slv.add(y-x == 2/3)
print(slv.check())
slv.pop()
