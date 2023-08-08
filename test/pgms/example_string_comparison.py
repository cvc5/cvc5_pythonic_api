from cvc5_pythonic_api import *
a, b, c = Strings('a b c')
solve(a<b,b<c)
solve(a>b,b<=c)
solve(a >= c, a<=b)

