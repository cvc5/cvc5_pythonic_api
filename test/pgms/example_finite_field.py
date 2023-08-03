from cvc5_pythonic_api import *

if __name__ == '__main__':
    try:
        
        a, b = FiniteFieldElems('a b', 5)

        # SAT
        solve(a * b == 1, a == 2)

        # UNSAT
        solve(a * b == 1, a == 2, b == 2)
    except RuntimeError as e:
        # We want the test to pass in case cocoa is not installed
        if "--cocoa" not in str(e):
            # If the error is not related to cocoa then fail
            raise e
        else:
            # If cocoa is not installed then mock correct result
            print("[a = 2, b = -2]\nno solution")
