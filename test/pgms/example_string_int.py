from cvc5_pythonic_api import *
a, b = Ints('a b')
solve(IntToStr(a)>IntToStr(b))
solve(StrFromCode(a) > StrFromCode(b))
c,d = Strings('c d')
solve(StrToInt(c)>StrToInt(d))
solve(StrToCode(c) > StrToCode(d))
