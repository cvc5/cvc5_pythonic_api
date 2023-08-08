from cvc5_pythonic_api import *


def mysolve(*args):
    s = Solver()
    print(s.check(*args))


s, t = Consts("s t", SeqSort(IntSort()))
print(is_seq(s))
mysolve(SeqUpdate(s, t, 0) == Concat(Unit(IntVal(1)), Unit(IntVal(2))))
a = String("a")
mysolve(SeqUpdate(a, StringVal("llo"), 2) == "hello")
