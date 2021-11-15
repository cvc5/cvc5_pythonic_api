from cvc5_z3py_compat import *

s = Solver()
s.set(**{'nl-ext': "none"})
a = Int('a')
solve_using(s, [a * a == 4])
