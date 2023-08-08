from cvc5_pythonic_api import *
n = String("trying")
b = String("B")
print(b.sort().is_string())
print(is_string(b))
solve(n==b)
