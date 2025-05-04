from cvc5 import ProofRule
from cvc5_pythonic_api import *

def collect_initial_assumptions(proof):
    # the initial assumptions are all the arguments of the initial
    # SCOPE applications in the proof
    proof_assumptions = []
    while (proof.getRule() == ProofRule.SCOPE):
        proof_assumptions += proof.getArguments()
        proof = proof.getChildren()[0]
    return proof_assumptions

def validate_proof_assumptions(assertions, proof_assumptions):
    # checks that the assumptions in the produced proof match the
    # assertions in the problem
    return sum([c in assertions for c in proof_assumptions]) == len(proof_assumptions)


p1, p2, p3 = Bools('p1 p2 p3')
x, y = Ints('x y')
s = Solver()
s.set('produce-proofs','true')
assertions = [p1, p2, p3, Implies(p1, x > 0), Implies(p2, y > x), Implies(p2, y < 1), Implies(p3, y > -3)]

for a in assertions:
    s.add(a)

print(s.check())

proof = s.proof()

proof_assumptions = collect_initial_assumptions(proof)

assert validate_proof_assumptions(assertions, proof_assumptions)
