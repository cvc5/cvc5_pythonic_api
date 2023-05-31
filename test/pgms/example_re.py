from cvc5_pythonic_api import *
r1 = Re('a')
r2 = Re('b')
print(is_re(r1))
a = String('a')
solve(InRe(a,Union(r1,r2)))
solve(InRe(a,Intersect(r1,r2)))
solve(InRe(a,Complement(r1)))
solve(InRe(a,Star(Union(r1,r2))))
