from cvc5_z3py_compat import *

if __name__ == '__main__':
    var = Bool('Hello World!')
    solve(var)
