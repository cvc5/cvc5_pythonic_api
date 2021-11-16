#!/usr/bin/env python3

if __name__ == "__main__":
    import doctest
    import cvc5_z3py_compat

    doctest.testmod(cvc5_z3py_compat.z3)
