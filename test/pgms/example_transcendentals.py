from cvc5_pythonic_api import *

if __name__ == '__main__':
    x, y = Reals("x y")
    solve(x > Pi(),
            x < 2 * Pi(),
            y ** 2 < Sine(x))
