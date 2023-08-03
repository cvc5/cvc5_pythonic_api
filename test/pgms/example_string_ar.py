from cvc5_pythonic_api import *
a = String('a')
solve(Length(a) == 5,a[0]==StringVal('a'))
solve(a.at(0)==StringVal('?'))
