#!/usr/bin/env python3

import sys

if __name__ == "__main__":
    import doctest
    import cvc5_pythonic_api

    n_failed, _ = doctest.testmod(cvc5_pythonic_api.cvc5_pythonic)
    if n_failed > 0:
        sys.exit(1)
