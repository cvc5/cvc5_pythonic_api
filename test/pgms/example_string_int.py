from cvc5_pythonic_api import *
a, b = Ints('a b')
solve(IntToStr(a)>IntToStr(b))
c,d = Strings('c d')
solve(StrToInt(c)>StrToInt(d))
