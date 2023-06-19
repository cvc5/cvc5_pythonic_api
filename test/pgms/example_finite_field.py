from cvc5_pythonic_api import *

if __name__ == '__main__':

    a, b = FiniteFieldElems('a b', 5)

    # SAT
    solve(a * b == 1, a == 2)

    # UNSAT
    solve(a * b == 1, a == 2, b == 2)
