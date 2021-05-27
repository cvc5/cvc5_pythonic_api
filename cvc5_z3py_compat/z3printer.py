############################################
# Copyright (c) 2021 The CVC5 Developers
#               2012 The Microsoft Corporation
#
# cvc5's Z3-compatible Python interface
#
# Author: Alex Ozdemir (aozdemir)
# pyz3 Author: Leonardo de Moura (leonardo)
############################################
import sys
import io

import itertools as it

from cvc5_z3py_compat import z3 as cvc
import pycvc5 as pc
from pycvc5 import kinds

# TODO: printer
