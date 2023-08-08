from cvc5_pythonic_api import *

x, y = Ints("x y")
a, b = BitVecs("a b", 4)
f = Function("f", BitVecSort(4), BitVecSort(4))

# implicit solver
solve(x == 2 * y, y == 2 * x)

# QF_NIA
s = SolverFor("QF_NIA")
print(s.check(x == 2 * y, y == 2 * x))
print(s.model()[x])

# QF_BV on BV
try:
    s = SolverFor("QF_BV")
    print(s.check(x == 2 * y, y == 2 * x))
    print(s.model()[x])
except Exception as e:
    print(e)
    print("Can't solve integer problems with QF_BV solver")


# QF_NIA
s = SolverFor("QF_BV")
print(s.check(a == 2 * b, b == 2 * a, a != b))

# QF_NIA
s = SolverFor("QF_BV")
s.setOption("bitblast", "eager")
print(s.check(a == 2 * b, b == 2 * a, a != b))

# Eager BB doesn't work with ALL
try:
    s = Solver()
    s.setOption("bitblast", "eager")
    print(s.check(a == 2 * b, b == 2 * a, a != b))
except Exception as e:
    print("Can't eagerly BB with models and ALL")
