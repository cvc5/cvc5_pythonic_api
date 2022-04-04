from cvc5_pythonic_api import *

if __name__ == '__main__':
    s = Solver()
    s.set(**{"produce-models": "true"})
    try:
        # invalid option
        s.set(**{"non-existing-option": "true"})
    except:
        pass

    try:
        # type error
        Int("x") + BitVec("a", 5)
    except:
        pass

    s += BoolVal(False)
    s.check()
    try:
        s.model()
    except:
        pass
