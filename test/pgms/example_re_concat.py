from cvc5_pythonic_api import *
s = String('s')
r1 = Re('a')
r2 = Re('b')
solve(InRe(s,Concat(r1,r2)))
solve(InRe(s,Concat(r1,Star(r2))))
