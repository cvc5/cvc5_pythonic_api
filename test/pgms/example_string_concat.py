from cvc5_pythonic_api import *
a = String('a')
b = String('b')
const = StringVal('hello')
solve(a == a+b)
solve(a == Concat(a,b),a == const)
solve(a == a+b, b == b+a, Length(a) > 0, Length(b) > 0 )
