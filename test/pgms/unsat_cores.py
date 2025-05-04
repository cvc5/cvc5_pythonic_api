from cvc5_pythonic_api import *


def reset_solver(s):
    s.reset()
    s.set('produce-unsat-cores','true')

def validate_unsat_core(input_formulas, core):
    # checks that the produced unsat core match the input formulas sent to the check function
    return sum([c in input_formulas for c in core]) == len(core)


def check_unsat_core(core):
    # This function checks whether the unsat core is unsatisfiable
    slvr = Solver()
    return s.check(*core) == unsat


# To make make sure the unsat_core function works there should be at least one nontrivial solution - a solution that doesn't contain all the assumptions sent in the check function.
nontrivial_counter = 0

p1, p2, p3 = Bools('p1 p2 p3')
x, y = Ints('x y')
s = Solver()
reset_solver(s)
assertions = [Implies(p1, x > 0), Implies(p2, y > x), Implies(p2, y < 1), Implies(p3, y > -3)]

for a in assertions:
    s.add(a)

assumptions = [p1,p2,p3]

s.check(*assumptions)

core = s.unsat_core()

assert validate_unsat_core(assertions + assumptions,core)
assert check_unsat_core(core)
if len(core) < len(assumptions) + len(assertions):
    nontrivial_counter += 1

# example 2 - booleans

reset_solver(s)

a, b, c = Bools('a b c')

# Add constraints

assertions = [Or(a, b), Or(Not(a), c), Not(c) ]
for c in assertions:
    s.add(c)


# Check satisfiability
assumptions = [a,b,c]
result = s.check(*assumptions)

core = s.unsat_core()

assert validate_unsat_core(assertions + assumptions, core)
assert check_unsat_core(core)
if len(core) < len(assumptions) + len(assertions):
    nontrivial_counter += 1

# example 3 - booleans


reset_solver(s)

a, b, c = Bools('a b c')
d = Bool('d')
# Add constraints with boolean operators
assertions = [And(a, b, Not(c)), Or(a, d), Not(And(a, d)) ]
for a in assertions:
    s.add(a)

# Check satisfiability
assumptions = [a,b,c,d]
result = s.check(*assumptions)

core = s.unsat_core()

assert validate_unsat_core(assumptions + assertions, core)
assert check_unsat_core(core)
if len(core) < len(assumptions) + len(assertions):
    nontrivial_counter += 1

# example 4 - reals



reset_solver(s)

x = Real('x')
y = Real('y')
z = Real('z')

assertions = [x + y == 5, y - z > 2, z > 3 ]
for a in assertions:
    s.add(a)

# Check satisfiability
assumptions = [x > 0, y > 0, z > 0]
result = s.check(*assumptions)

core = s.unsat_core()

assert validate_unsat_core(assumptions + assertions, core)
assert check_unsat_core(core)
if len(core) < len(assumptions) + len(assertions):
    nontrivial_counter += 1


# example 5 - strings


reset_solver(s)


# Define string variables
s1 = String('s1')
s2 = String('s2')

# Add string constraints
assertions = [Or(s1 == "hello", s1 == "world"), s1 + s2 == "helloworld"]
for a in assertions:
    s.add(a)

# Check satisfiability

result = s.check( Length(s2) < 2)

core = s.unsat_core()

assert validate_unsat_core([Length(s2) < 2] + assertions, core)
assert check_unsat_core(core)
if len(core) < len([ Length(s2) < 2 ]) + len(assertions):
    nontrivial_counter += 1

# check that there is at least one nontrivial unsat core
assert nontrivial_counter >= 1

print('success')
