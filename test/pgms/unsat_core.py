from cvc5_pythonic_api import *
#from z3 import *


def reset_solver(s):
    s.reset()
    s.set('produce-unsat-assumptions','true')

p1, p2, p3 = Bools('p1 p2 p3')
x, y = Ints('x y')
s = Solver()
s.set('produce-unsat-assumptions','true')
s.add(Implies(p1, x > 0))
s.add(Implies(p2, y > x))
s.add(Implies(p2, y < 1))
s.add(Implies(p3, y > -3))
print(s.check(p1,p2,p3))

core = s.unsat_core()
print(core)
print("p1 in core: ", p1 in core)
print("p2 in core: ", p2 in core)
print("p3 in core: ", p3 in core)

# example 2 - booleans

print('-------------------------')

reset_solver(s)

a, b, c = Bools('a b c')

# Add constraints
s.add(Or(a, b))
s.add(Or(Not(a), c))
s.add(Not(c))


# Check satisfiability
result = s.check(a,b,c)

if result == unsat:
    print("Formula is unsatisfiable")
    # Retrieve and print unsat core
    unsat_core = s.unsat_core()
    print("Unsatisfiable core:", unsat_core)
else:
    print("Formula is satisfiable")

# example 3 - booleans

print('-------------------------')

reset_solver(s)


d = Bool('d')
# Add constraints with boolean operators
s.add(And(a, b, Not(c)))
s.add(Or(a, d))
s.add(Not(And(a, d)))

# Check satisfiability
result = s.check(a,b,c,d)

if result == unsat:
    print("Formula is unsatisfiable")
    # Retrieve and print unsat core
    unsat_core = s.unsat_core()
    print("Unsatisfiable core:", unsat_core)
else:
    print("Formula is satisfiable")


# example 4 - reals

print('-------------------------')

reset_solver(s)

x = Real('x')
y = Real('y')
z = Real('z')
s.add(x + y == 5)
s.add(y - z > 2)
s.add(z > 3)

# Check satisfiability
result = s.check(x > 0, y > 0, z > 0)

if result == unsat:
    print("Constraints are unsatisfiable.")
    unsat_core = s.unsat_core()
    print("Unsatisfiable core:", unsat_core)
else:
    print("Constraints are satisfiable.")
    

# example 5 - strings

print('-------------------------')

reset_solver(s)


# Define string variables
s1 = String('s1')
s2 = String('s2')

# Add string constraints
s.add(Or(s1 == "hello", s1 == "world"))
# s.add(s2 == "goodbye")
s.add(s1 + s2 == "helloworld")

# Check satisfiability
result = s.check( Length(s2) < 2)

if result == unsat:
    print("Constraints are unsatisfiable.")
    unsat_core = s.unsat_core()
    print("Unsatisfiable core:", unsat_core)
else:
    print("Constraints are satisfiable.")



