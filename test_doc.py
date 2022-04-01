#!/usr/bin/env python3

import sys

if __name__ == "__main__":
    import doctest
    import cvc5_z3py_compat

    n_failed, _ = doctest.testmod(cvc5_z3py_compat.z3)
    if n_failed > 0:
        sys.exit(1)
