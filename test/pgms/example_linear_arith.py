from cvc5_z3py_compat import *

slv = SolverFor('QF_LIRA')

x = Int('x')
y = Real('y')

slv.asssert(And(x >= 3 * y, x <= y, -2 < x))
slv.push()
slv.check(y-x <= 2/3)
slv.pop()
slv.assert(y-x == 2/3)
slv.check()
slv.pop()