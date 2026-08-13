from cvc5_pythonic_api import *

# A function whose range is the sort of a lambda: the sort is flattened, so
# saturating the leading domains yields the range sort back.
Interval = Datatype('Interval')
Interval.declare('mk', ('lo', RealSort()), ('hi', RealSort()))
Interval = Interval.create()

i = Const('i', Interval)
x = Real('x')
body = Lambda([x], And(Interval.lo(i) <= x, x <= Interval.hi(i)))

setof = Function('setof', Interval, body.sort())
print(setof.sort())
print(setof(i).sort())
print(setof(i).sort() == body.sort())

# Partial applications print as ordinary applications.
print(setof(i))
print(setof(i)(x))

# The definition a Z3Py `define` would build now typechecks.
defn = ForAll([i], setof(i) == body)
print(defn)

# ... and is usable, under a higher-order logic.
s = SolverFor('HO_ALL')
s.set('ho-elim', True)
s.add(defn)
s.add(Not(setof(Interval.mk(0, 10))(3)))
print(s.check())

s = SolverFor('HO_ALL')
s.set('ho-elim', True)
s.add(defn)
s.add(setof(Interval.mk(0, 10))(42))
print(s.check())

# Currying an ordinary function agrees with applying it outright.
f = Function('f', IntSort(), IntSort(), IntSort())
y = Int('y')
print(f(y)(y).eq(f(y, y)))
s = SolverFor('HO_ALL')
s.add(f(y)(y) != f(y, y))
print(s.check())

# The head of an application need not be a name.
g = Function('g', IntSort(), IntSort(), IntSort())
print(If(Bool('c'), f, g)(y))
print(If(Bool('c'), f, g)(y)(y))
