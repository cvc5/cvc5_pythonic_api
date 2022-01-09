from cvc5_z3py_compat import *

# Introduce existential real and integer variables
x, y = Reals("x y")
a, b = Ints("a b")

# Our constraints regarding x and y will be:
#
#   (1)  0 < x
#   (2)  0 < y
#   (3)  x + y < 1
#   (4)  x <= y
s = Solver()
s += 0 < x
s += 0 < y
s += x + y < 1
s += x <= y

# We can check if these constraints are satisfiable.
assert sat == s.check()

# We can ask the solver for a *model* (a satisfying assignment), and evaluate
# terms using that assignment.
m = s.model()
print("model: ", m)
print("x - y: ", m[x - y])

# Let's repeat these constraints, with integers...
s.reset()
s += 0 < a
s += 0 < b
s += a + b < 1
s += a <= b

# Now, the constraints are UNSAT
assert unsat == s.check()
