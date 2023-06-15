from cvc5_pythonic_api import *
#from z3 import *
s, t, u = Consts('s t u', SeqSort(IntSort()))
solve(Concat(s, Unit(IntVal(2))) == Concat(Unit(IntVal(1)), t))
# [] at
solve(PrefixOf(s,Concat(Unit(IntVal(1)),Unit(IntVal(2)))))
solve(PrefixOf(Concat(Unit(IntVal(1)),Unit(IntVal(2))),s))
solve(SuffixOf(s,Concat(Unit(IntVal(1)),Unit(IntVal(2)))))
solve(SuffixOf(Concat(Unit(IntVal(1)),Unit(IntVal(2))),s))
solve(Contains(s,t),Length(t)>1)
solve(Replace(s,t,u)==Replace(s,u,t))
solve(IndexOf(s,t) == 1 )
solve(IndexOf(s,t,1) > 1 )
