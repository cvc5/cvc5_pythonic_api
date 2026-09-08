from cvc5_pythonic_api import *

# A fresh name is fresh across sorts, not just within one. Sharing a name
# with a constant of another sort would make the two indistinguishable once
# printed, and the assertions below unparseable: the name would appear
# applied at both sorts, which no set of declarations can typecheck.
a = FreshConst(Float16())
b = FreshConst(Float16())
c = FreshConst(Float32())
print(a, b, c)

s = Solver()
s.add(fpIsNormal(a))
s.add(fpIsNormal(b))
s.add(fpIsSubnormal(c))
ab = fpMul(RTZ(), fpToFP(RTZ(), a, Float32()), fpToFP(RTZ(), b, Float32()))
s.add(fpIsNormal(fpAdd(RTZ(), ab, c)))
print(s.sexpr())

# Distinct terms, whatever they are called.
print(a.eq(b), a.eq(c), b.eq(c))

# The other Fresh* helpers draw from the same counter, so a name minted by
# one is never handed out by another. FreshBool and FreshReal both default
# to the "b" prefix, so nothing but the counter keeps them apart.
print(FreshBool(), FreshInt(), FreshReal(), FreshConst(IntSort()))
print(FreshFunction(IntSort(), IntSort()))

# The prefix is honored, and a number is never reused within one either.
print(FreshConst(BoolSort(), prefix="test"), FreshConst(BoolSort(), prefix="test"))

# A declared constant blocks its name for every sort, not just its own: the
# counter has reached 10 by now, so the fresh Bool below skips the name an
# Int already holds.
Int("b10")
print(FreshBool())
