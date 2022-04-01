from cvc5_pythonic_api import *

s = Solver()
s.set(**{'nl-ext': "none"})
a = Int('a')
solve_using(s, [a * a == 4])
