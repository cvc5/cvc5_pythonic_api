from cvc5_pythonic_api import *
#from z3 import *
a, b, c = Strings('a b c')
solve(a<b,b<c)
solve(a>b,b<=c)
solve(a >= c, a<=b)
solve(a>b,b>c,c>a)

