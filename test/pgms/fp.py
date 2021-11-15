from cvc5_z3py_compat import *

x_signed = BitVecVal(-5, BitVecSort(32))
x_fp = fpSignedToFP(RNE(), x_signed, Float32())
print(x_fp)
