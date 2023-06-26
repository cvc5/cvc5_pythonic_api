from cvc5_pythonic_api import *
s,t = Consts('s t',SeqSort(IntSort()))
print(is_seq(s))
solve(SeqUpdate(s,t,0) == Concat(Unit(IntVal(1)),Unit(IntVal(2))))
a = String('a')
solve(SeqUpdate(a,StringVal('llo'),2) == 'hello')
