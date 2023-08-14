from cvc5_pythonic_api import *

s, t, u = Consts("s t u", SeqSort(IntSort()))
print(s.is_string())


def mysolve(*args):
    s = Solver()
    print(s.check(*args))


mysolve(Concat(s, Unit(IntVal(2))) == Concat(Unit(IntVal(1)), t))
mysolve(PrefixOf(s.at(0), t), Length(s) > 0)
mysolve(s[0] > 5)
mysolve(PrefixOf(s, Concat(Unit(IntVal(1)), Unit(IntVal(2)))))
mysolve(PrefixOf(Concat(Unit(IntVal(1)), Unit(IntVal(2))), s))
mysolve(SuffixOf(s, Concat(Unit(IntVal(1)), Unit(IntVal(2)))))
mysolve(SuffixOf(Concat(Unit(IntVal(1)), Unit(IntVal(2))), s))
mysolve(Contains(s, t), Length(t) > 1)
mysolve(Replace(s, t, u) == Replace(s, u, t))
mysolve(IndexOf(s, t) == 1)
mysolve(IndexOf(s, t, 1) > 1)
e = Empty(SeqSort(IntSort()))
mysolve(PrefixOf(s, e))
