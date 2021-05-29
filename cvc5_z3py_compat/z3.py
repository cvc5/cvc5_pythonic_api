############################################
# Copyright (c) 2021 The cvc5 Developers
#               2012 The Microsoft Corporation
#
# cvc5's Z3-compatible Python interface
#
# Author: Alex Ozdemir (aozdemir)
# pyz3 Author: Leonardo de Moura (leonardo)
############################################

"""
cvc5 is an SMT solver.

This is its (as much as possible) Z3-compatible python interface.

Several online tutorials for Z3Py are available at:
http://rise4fun.com/Z3Py/tutorial/guide

Please send feedback, comments and/or corrections on the Issue tracker for
https://github.com/cvc5/cvc5.git. Your comments are very valuable.

TODO: example

"""

from .z3printer import *
from fractions import Fraction
from decimal import Decimal
import decimal
import sys
import io
import math
import copy
import functools as ft
import operator as op

import pycvc5 as pc
from pycvc5 import kinds

DEBUG = __debug__


def debugging():
    global DEBUG
    return DEBUG


def _is_int(v):
    """Python 2/3 agnostic int testing"""
    if sys.version < "3":
        return isinstance(v, (int, long))  # type: ignore
    else:
        return isinstance(v, int)


def unimplemented(msg=None):
    if msg is None:
        raise Exception("Unimplemented")
    else:
        raise Exception("Unimplemented: {}".format(msg))


class SMTException(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


# We use _assert instead of the assert command because we want to
# use our own exception class
def _assert(cond, msg):
    if not cond:
        raise SMTException(msg)


# Hack for having nary functions that can receive one argument that is the
# list of arguments.
# Use this when function takes a single list of arguments
def _get_args(args):
    try:
        if len(args) == 1 and isinstance(args[0], (list, tuple)):
            return list(args[0])
        else:
            return list(args)
    except TypeError:
        # len is not necessarily defined when args is not a sequence
        return list(args)


class Context(object):
    """A Context manages all terms, configurations, etc.

    In cvc5's API, these are managed by a solver, but we keep the Context class
    (which just wraps a solver) for compatiblity.

    It's only responsibilities are:
        * making fresh identifiers for a given sort
        * looking up previously defined constants
    """

    def __init__(self, *args, **kws):
        self.solver = pc.Solver()
        self.solver.setOption("produce-models", "true")
        # Map from (name, sort) pairs to constant terms
        self.vars = {}
        # An increasing identifier used to make fresh identifiers
        self.next_fresh_var = 0

    def __del__(self):
        self.solver = None

    def get_var(self, name, sort):
        """Get the variable identified by `name`.

        If no variable of that name (with that sort) has been created, creates
        one.

        Returns a Term
        """
        if (name, sort) not in self.vars:
            self.vars[(name, sort)] = self.solver.mkConst(sort.ast, name)
        return self.vars[(name, sort)]

    def next_fresh(self, sort, prefix):
        """Make a name such that (name, sort) is fresh.

        The name will be prefixed by `prefix`"""
        name = "{}{}".format(prefix, self.next_fresh_var)
        while (name, sort) in self.vars:
            self.next_fresh_var += 1
            name = "{}{}".format(prefix, self.next_fresh_var)
        return name

    def __eq__(self, o):
        return self.solver is o.solver


# Global SMT context
_main_ctx = None


def main_ctx():
    """Return a reference to the global context.

    >>> x = Real('x')
    >>> x.ctx == main_ctx()
    True
    >>> c = Context()
    >>> c == main_ctx()
    False
    >>> x2 = Real('x', c)
    >>> x2.ctx == c
    True
    >>> eq(x, x2)
    False
    """
    global _main_ctx
    if _main_ctx is None:
        _main_ctx = Context()
    return _main_ctx


def _get_ctx(ctx):
    if ctx is None:
        return main_ctx()
    else:
        return ctx


def get_ctx(ctx):
    return _get_ctx(ctx)


#########################################
#
# Term base class
#
#########################################


class ExprRef(object):
    """Constraints, formulas and terms are expressions."""

    def __init__(self, ast, ctx=None, reverse_children=False):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        self.reverse_children = reverse_children
        assert isinstance(self.ast, pc.Term)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None and self.ast is not None:
            self.ctx = None
            self.ast = None

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> x = Int('x')
        >>> ((x + 1)*x).sexpr()
        '(* (+ x 1) x)'
        """
        return str(self.ast)

    def as_ast(self):
        """Return a pointer to the underlying Term object."""
        return self.ast

    def get_id(self):
        """Return unique identifier for object.
        It can be used for hash-tables and maps."""
        return self.ast.getId()

    def eq(self, other):
        """Return `True` if `self` and `other` are structurally identical.

        >>> x = Int('x')
        >>> n1 = x + 1
        >>> n2 = 1 + x
        >>> n1.eq(n2)
        False
        """
        if debugging():
            _assert(is_ast(other), "SMT AST expected")
        return self.ctx == other.ctx and self.as_ast() == other.as_ast()

    def hash(self):
        """Return a hashcode for the `self`.

        >>> n1 = Int('x') + 1
        >>> n2 = Int('x') + 1
        >>> n1.hash() == n2.hash()
        True
        """
        return self.as_ast().__hash__()

    def sort(self):
        """Return the sort of expression `self`.

        >>> x = Int('x')
        >>> (x + 1).sort()
        Int
        >>> y = Real('y')
        >>> (x + y).sort()
        Real
        """
        return _sort(self.ctx, self.ast)

    def __hash__(self):
        """Hash code."""
        return self.ast.__hash__()

    def params(self):
        return self.decl().params()

    def decl(self):
        """Return the SMT function declaration associated with an SMT application.

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> eq(t.decl(), f)
        True
        """
        if is_app_of(self, kinds.ApplyUf):
            return _to_expr_ref(list(self.ast)[0], self.ctx)  # type: ignore
        else:
            unimplemented("Declarations for non-function applications")

    def kind(self):
        """Return the kinds of this term

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> t.kind() == kinds.ApplyUf
        True
        """
        return self.ast.getKind()

    def num_args(self):
        """Return the number of arguments of an SMT application.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> (a + b).num_args()
        2
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.num_args()
        3
        """
        if debugging():
            _assert(is_app(self), "SMT application expected")
        if is_app_of(self, kinds.ApplyUf):
            return len(list(self.as_ast())) - 1  # type: ignore
        else:
            return len(list(self.as_ast()))  # type: ignore

    def arg(self, idx):
        """Return argument `idx` of the application `self`.

        This method assumes that `self` is a function application with at least
        `idx+1` arguments.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.arg(0)
        a
        >>> t.arg(1)
        b
        >>> t.arg(2)
        0
        """
        if debugging():
            _assert(is_app(self), "SMT application expected")
            _assert(idx < self.num_args(), "Invalid argument index")
        if is_app_of(self, kinds.ApplyUf):
            return _to_expr_ref(self.as_ast()[idx + 1], self.ctx)
        elif self.reverse_children:
            return _to_expr_ref(self.as_ast()[self.num_args() - (idx + 1)], self.ctx)
        else:
            return _to_expr_ref(self.as_ast()[idx], self.ctx)

    def children(self):
        """Return a list containing the children of the given expression

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.children()
        [a, b, 0]
        """
        if is_app_of(self, kinds.ApplyUf):
            return [_to_expr_ref(a, self.ctx) for a in list(self.ast)[1:]]  # type: ignore
        else:
            if is_app(self):
                args = list(self.ast)  # type: ignore
                if self.reverse_children:
                    args = reversed(args)
                return [_to_expr_ref(a, self.ctx) for a in args]
            else:
                return []


def is_ast(a):
    """Return `True` for expressions and sorts.

    Exposed by the Z3 API. Less relevant to us.

    >>> is_ast(10)
    False
    >>> is_ast(IntVal(10))
    True
    >>> is_ast(Int('x'))
    True
    >>> is_ast(BoolSort())
    True
    >>> is_ast(Function('f', IntSort(), IntSort()))
    True
    >>> is_ast("x")
    False
    >>> is_ast(Solver())
    False
    """
    return isinstance(a, (ExprRef, SortRef))


def eq(a, b):
    """Return `True` if `a` and `b` are structurally identical AST nodes.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> eq(x, y)
    False
    >>> eq(x + 1, x + 1)
    True
    >>> eq(x + 1, 1 + x)
    False
    """
    if debugging():
        _assert(is_ast(a) and is_ast(b), "SMT ASTs expected")
    return a.eq(b)


def _ctx_from_ast_arg_list(args, default_ctx=None):
    ctx = None
    for a in args:
        if is_ast(a):
            if ctx is None:
                ctx = a.ctx
            else:
                if debugging():
                    _assert(ctx == a.ctx, "Context mismatch")
    if ctx is None:
        ctx = default_ctx
    return ctx


def _ctx_from_ast_args(*args):
    return _ctx_from_ast_arg_list(args)


#########################################
#
# Sorts
#
#########################################


class SortRef(object):
    """A Sort is essentially a type. Every term has a sort"""

    def __init__(self, ast, ctx=None):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        assert isinstance(self.ast, pc.Sort)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None:
            self.ctx = None
        if self.ast is not None:
            self.ast = None

    def __eq__(self, other):
        return self.ast == other.ast

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> x = Int('x')
        >>> ((x + 1)*x).sexpr()
        '(* (+ x 1) x)'
        """
        return str(self.ast)

    def as_ast(self):
        """Return a pointer to the underlying Sort object."""
        return self.ast

    def eq(self, other):
        """Return `True` if `self` and `other` are structurally identical.

        >>> x = Int('x')
        >>> n1 = x + 1
        >>> n2 = 1 + x
        >>> n1.eq(n2)
        False
        >>> n1.eq(x + 1)
        True
        """
        instance_check(other, SortRef)
        assert self.ctx == other.ctx
        return self.as_ast() == other.as_ast()

    def hash(self):
        """Return a hashcode for the `self`.

        >>> n1 = Int('x') + 1
        >>> n2 = Int('x') + 1
        >>> n1.hash() == n2.hash()
        True
        """
        return self.as_ast().__hash__()

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`.

        >>> IntSort().subsort(RealSort())
        True
        """
        # subclasses override
        return False

    def cast(self, val):
        """Try to cast `val` as an element of sort `self`.

        This method is used in SMT to convert Python objects such as integers,
        floats, longs and strings into SMT expressions.

        >>> x = Int('x')
        >>> RealSort().cast(x)
        ToReal(x)
        """
        if debugging():
            _assert(is_expr(val), "SMT expression expected")
            _assert(self.eq(val.sort()), "Sort mismatch")
        # subclasses override
        return val

    def name(self):
        """Return the name (string) of sort `self`.

        >>> BoolSort().name()
        'Bool'
        >>> ArraySort(IntSort(), IntSort()).name()
        '(Array Int Int)'
        """
        return str(self.ast)

    def __ne__(self, other):
        """Return `True` if `self` and `other` are not the same SMT sort.

        >>> p = Bool('p')
        >>> p.sort() != BoolSort()
        False
        >>> p.sort() != IntSort()
        True
        """
        return self.ast != other.ast

    def __hash__(self):
        """Hash code."""
        return self.ast.__hash__()


def _sort(ctx, a):
    if isinstance(a, ExprRef):
        a = a.ast
    instance_check(a, pc.Term)
    return _to_sort_ref(a.getSort(), ctx)


def DeclareSort(name, ctx=None):
    """Create a new uninterpreted sort named `name`.

    If `ctx=None`, then the new sort is declared in the global SMT context.

    >>> A = DeclareSort('A')
    >>> a = Const('a', A)
    >>> b = Const('b', A)
    >>> a.sort() == A
    True
    >>> b.sort() == A
    True
    >>> a == b
    a == b
    """
    ctx = _get_ctx(ctx)
    return SortRef(ctx.solver.mkUninterpretedSort(name), ctx)


def is_sort(s):
    """Return `True` if `s` is an SMT sort.

    >>> is_sort(IntSort())
    True
    >>> is_sort(Int('x'))
    False
    >>> is_expr(Int('x'))
    True
    """
    return isinstance(s, SortRef)


def instance_check(item, instance):
    _assert(
        isinstance(item, instance),
        "Expected {}, but got a {}".format(instance, type(item)),
    )


def _to_sort_ref(s, ctx):
    """Construct the correct SortRef subclass for `s`

    s may be a base Sort or a SortRef.
    """
    if isinstance(s, SortRef):
        s = s.ast
    if debugging():
        instance_check(s, pc.Sort)
    if s.isBoolean():
        return BoolSortRef(s, ctx)
    elif s.isInteger() or s.isReal():
        return ArithSortRef(s, ctx)
    elif s.isBitVector():
        return BitVecSortRef(s, ctx)
    elif s.isArray():
        return ArraySortRef(s, ctx)
    elif s.isSet():
        return SetSortRef(s, ctx)
    return SortRef(s, ctx)


#########################################
#
# Function Declarations
#
#########################################


class FuncDeclRef(ExprRef):
    """Function declaration.
    Every constant and function have an associated declaration.

    The declaration assigns a name, a sort (i.e., type), and for function
    the sort (i.e., type) of each of its arguments. Note that, in SMT,
    a constant is a function with 0 arguments.
    """


#########################################
#
# Expressions
#
#########################################


def _to_expr_ref(a, ctx, r=None):
    """Construct the correct ExprRef subclass for `a`

    a may be a base Term or a ExprRef.

    Based on the underlying sort of a.
    """
    if isinstance(a, ExprRef):
        ast = a.ast
        if r is None:
            r = a.reverse_children
    elif isinstance(a, pc.Term):
        if r is None:
            r = False
        ast = a
    else:
        raise SMTException("Non-term/expression given to _to_expr_ref")
    sort = ast.getSort()
    if sort.isBoolean():
        return BoolRef(ast, ctx, r)
    if sort.isInteger():
        if ast.getKind() == kinds.ConstRational:
            return IntNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isReal():
        if ast.getKind() == kinds.ConstRational:
            return RatNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isBitVector():
        if ast.getKind() == kinds.ConstBV:
            return BitVecNumRef(ast, ctx, r)
        else:
            return BitVecRef(ast, ctx, r)
    if sort.isArray():
        return ArrayRef(ast, ctx, r)
    if sort.isSet():
        return SetRef(ast, ctx, r)
    return ExprRef(ast, ctx, r)


def is_expr(a):
    """Return `True` if `a` is an SMT expression.

    >>> a = Int('a')
    >>> is_expr(a)
    True
    >>> is_expr(a + 1)
    True
    >>> is_expr(IntSort())
    False
    >>> is_expr(1)
    False
    >>> is_expr(IntVal(1))
    True
    >>> x = Int('x')
    """
    return isinstance(a, ExprRef)


def is_app(a):
    """Return `True` if `a` is an SMT function application.

    Note that, constants are function applications with 0 arguments.

    >>> a = Int('a')
    >>> is_app(a)
    True
    >>> is_app(a + 1)
    True
    >>> is_app(IntSort())
    False
    >>> is_app(1)
    False
    >>> is_app(IntVal(1))
    True
    >>> x = Int('x')
    """
    # Change later for quantifiers
    return is_expr(a)


def is_app_of(a, k):
    """Return `True` if `a` is an application of the given kind `k`.

    >>> x = Int('x')
    >>> n = x + 1
    >>> is_app_of(n, kinds.Plus)
    True
    >>> is_app_of(n, kinds.Mult)
    False
    """
    return is_expr(a) and a.ast.getKind() == k


def Const(name, sort):
    """Create a constant of the given sort.

    >>> Const('x', IntSort())
    x
    """
    if debugging():
        _assert(isinstance(sort, SortRef), "SMT sort expected")
    ctx = sort.ctx
    e = ctx.get_var(name, sort)
    return _to_expr_ref(e, ctx)


def Consts(names, sort):
    """Create several constants of the given sort.

    `names` is a string containing the names of all constants to be created.
    Blank spaces separate the names of different constants.

    >>> x, y, z = Consts('x y z', IntSort())
    >>> x + y + z
    x + y + z
    """
    if isinstance(names, str):
        names = names.split(" ")
    return [Const(name, sort) for name in names]


def FreshConst(sort, prefix="c"):
    """Create a fresh constant of a specified sort"""
    ctx = sort.ctx
    name = ctx.next_fresh(sort, prefix)
    return Const(name, sort)


#########################################
#
# Booleans
#
#########################################


class BoolSortRef(SortRef):
    """Boolean sort."""


class BoolRef(ExprRef):
    """All Boolean expressions are instances of this class."""

    def sort(self):
        return _sort(self.ctx, self.ast)


def BoolSort(ctx=None):
    """Return the Boolean SMT sort. If `ctx=None`, then the global context is used.

    >>> BoolSort()
    Bool
    >>> p = Const('p', BoolSort())
    >>> is_bool(p)
    True
    >>> r = Function('r', IntSort(), IntSort(), BoolSort())
    >>> r(0, 1)
    r(0, 1)
    >>> is_bool(r(0, 1))
    True
    """
    ctx = _get_ctx(ctx)
    return BoolSortRef(ctx.solver.getBooleanSort(), ctx)


#########################################
#
# Arithmetic
#
#########################################


class ArithSortRef(SortRef):
    """Real and Integer sorts."""


class ArithRef(ExprRef):
    """Integer and Real expressions."""


class IntNumRef(ArithRef):
    """Integer values."""


class RatNumRef(ArithRef):
    """Rational values."""


#########################################
#
# Bit-Vectors
#
#########################################


class BitVecSortRef(SortRef):
    """Bit-vector sort."""


class BitVecRef(ExprRef):
    """Bit-vector expressions."""


class BitVecNumRef(BitVecRef):
    """Bit-vector values."""


#########################################
#
# Arrays
#
#########################################


class ArraySortRef(SortRef):
    """Array sorts."""


class ArrayRef(ExprRef):
    """Array expressions."""


#########################################
#
# Sets
#
#########################################


class SetSortRef(SortRef):
    """Array sorts."""


class SetRef(ExprRef):
    """Array expressions."""


#########################################
#
# Solver
#
#########################################
class CheckSatResult(object):
    """Represents the result of a satisfiability check: sat, unsat, unknown.

    >>> s = Solver()
    >>> s.check()
    sat
    >>> r = s.check()
    >>> isinstance(r, CheckSatResult)
    True
    """

    def __init__(self, r):
        instance_check(r, pc.Result)
        self.r = r

    def __deepcopy__(self, memo={}):
        return CheckSatResult(self.r)

    def __eq__(self, other):
        return repr(self) == repr(other)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if self.r.isSat():
            return "sat"
        elif self.r.isUnsat():
            return "unsat"
        else:
            return "unknown"


class CheckSatResultLiteral(CheckSatResult):
    """Represents the literal result of a satisfiability check: sat, unsat,
    unknown.

    >>> s = Solver()
    >>> s.check()
    sat
    >>> s.check() == CheckSatResultLiteral("sat")
    True
    """

    def __init__(self, string):
        self.string = string

    def __deepcopy__(self, memo={}):
        return CheckSatResultLiteral(self.string)

    def __repr__(self):
        return self.string


sat = CheckSatResultLiteral("sat")
unsat = CheckSatResultLiteral("unsat")
unknown = CheckSatResultLiteral("unknown")


class Solver(object):
    """Solver API provides methods for implementing the main SMT 2.0 commands:
    * push,
    * pop,
    * check,
    * get-model,
    * etc."""

    def __init__(self, solver=None, ctx=None, logFile=None):
        assert solver is None or ctx is not None
        self.ctx = _get_ctx(ctx)
        self.solver = self.ctx.solver
        self.scopes = 0
        self.assertions_ = [[]]
        self.last_result = None
        self.reset()

    def __del__(self):
        if self.solver is not None:
            self.solver = None
        if self.ctx is not None:
            self.ctx = None

    def push(self):
        """Create a backtracking point.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        self.scopes += 1
        self.assertions_.append([])
        self.solver.push(1)

    def pop(self, num=1):
        """Backtrack num backtracking points.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        assert num <= self.scopes
        self.scopes -= num
        for _ in range(num):
            self.assertions_.pop()
        self.solver.pop(num)

    def num_scopes(self):
        """Return the current number of backtracking points.

        >>> s = Solver()
        >>> s.num_scopes()
        0
        >>> s.push()
        >>> s.num_scopes()
        1
        >>> s.push()
        >>> s.num_scopes()
        2
        >>> s.pop()
        >>> s.num_scopes()
        1
        """
        return self.scopes

    def reset(self):
        """Remove all asserted constraints and backtracking points created
        using `push()`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.reset()
        >>> s
        []
        """
        self.solver.resetAssertions()
        self.scopes = 0
        self.assertions_ = [[]]

    def assert_exprs(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.assert_exprs(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        args = _get_args(args)
        s = BoolSort(self.ctx)
        for arg in args:
            arg = s.cast(arg)
            self.assertions_[-1].append(arg)
            self.solver.assertFormula(arg.ast)

    def add(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def __iadd__(self, fml):
        self.add(fml)
        return self

    def append(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.append(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def insert(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.insert(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def check(self, *assumptions):
        """Check whether the assertions in the given solver plus the optional
        assumptions are consistent or not.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.check()
        sat
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> s.model().eval(x)
        1
        >>> s.add(x < 1)
        >>> s.check()
        unsat
        >>> s.reset()
        """
        assumptions = _get_args(assumptions)
        r = CheckSatResult(self.solver.checkSatAssuming(*[a.ast for a in assumptions]))
        self.last_result = r
        return r

    def model(self):
        """Return a model for the last `check()`.

        This function raises an exception if
        a model is not available (e.g., last `check()` returned unsat).

        >>> s = Solver()
        >>> a = Int('a')
        >>> s.add(a + 2 == 0)
        >>> s.check()
        sat
        >>> s.model()
        [a = -2]
        """
        return ModelRef(self, self.ctx)

    def assertions(self):
        """Return an AST vector containing all added constraints.

        >>> s = Solver()
        >>> s.assertions()
        []
        >>> a = Int('a')
        >>> s.add(a > 0)
        >>> s.add(a < 10)
        >>> s.assertions()
        [a > 0, a < 10]
        """
        return ft.reduce(op.add, self.assertions_)

    def reason_unknown(self):
        """Return a string describing why the last `check()` returned `unknown`.

        >>> x = Int('x')
        >>> s = SimpleSolver()
        """
        if self.last_result is None:
            raise SMTException("No previous check-sat call, so no reason for unknown")
        return self.last_result.r.getUnknownExplanation()

    def __repr__(self):
        """Return a formatted string with all added constraints."""
        return "[" + ", ".join(str(a) for a in self.assertions()) + "]"

    def sexpr(self):
        """Return a formatted string (in Lisp-like format) with all added
        constraints. We say the string is in s-expression format.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s.add(x < 2)
        >>> r = s.sexpr()
        """
        return "(and " + " ".join(a.sexpr() for a in self.assertions()) + ")"


def SolverFor(logic, ctx=None, logFile=None):
    """Create a solver customized for the given logic.

    The parameter `logic` is a string. It should be the name of an SMT-LIB
    logic.
    See http://www.smtlib.org/ for the name of all available logics.
    """

    # Pending multiple solvers
    #     >>> s = SolverFor("QF_LIA")
    #     >>> x = Int('x')
    #     >>> s.add(x > 0)
    #     >>> s.add(x < 2)
    #     >>> s.check()
    #     sat
    #     >>> s.model()
    #     [x = 1]
    #     """
    solver = pc.Solver()
    solver.setLogic(logic)
    ctx = _get_ctx(ctx)
    return Solver(solver, ctx, logFile)


def SimpleSolver(ctx=None, logFile=None):
    """Return a simple general purpose solver.

    >>> s = SimpleSolver()
    >>> x = Int('x')
    >>> s.add(x > 0)
    >>> s.check()
    sat
    """
    ctx = _get_ctx(ctx)
    return Solver(None, ctx, logFile)


#########################################
#
# Utils
#
#########################################


class ModelRef:
    """Model/Solution of a satisfiability problem (aka system of constraints)."""

    def __init__(self, solver, ctx):
        assert solver is not None
        assert ctx is not None
        self.solver = solver
        self.ctx = ctx

    def __del__(self):
        if self.solver is not None:
            self.solver = None
        if self.ctx is not None:
            self.ctx = None

    def vars(self):
        """Returns the free constants in an assertion, as terms"""
        visit = {a: True for a in self.solver.assertions()}
        q = list(visit.keys())
        vars_ = set()
        while len(q) > 0:
            a = q.pop()
            if a.ast.getKind() == kinds.Constant:
                vars_.add(a)
            else:
                for c in a.children():
                    if c not in visit:
                        visit[c] = True
                        q.append(c)
                if a.kind() == kinds.ApplyUf:
                    c = a.decl()
                    if c not in visit:
                        visit[c] = True
                        q.append(c)

        return vars_

    def __repr__(self):
        var_vals = [(str(v), self[v]) for v in self.decls()]
        inner = ", ".join(
            v + " = " + str(val) for v, val in sorted(var_vals, key=lambda a: a[0])
        )
        return "[" + inner + "]"

    def eval(self, t, model_completion=False):
        """Evaluate the expression `t` in the model `self`. If
        `model_completion` is enabled, then a default interpretation is
        automatically added for symbols that do not have an interpretation in
        the model `self`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.eval(x + 1)
        2
        >>> m.eval(x == 1)
        True
        """
        return _to_expr_ref(self.solver.solver.getValue(t.ast), self.solver.ctx)

    def evaluate(self, t, model_completion=False):
        """Alias for `eval`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.evaluate(x + 1)
        2
        >>> m.evaluate(x == 1)
        True
        """
        return self.eval(t, model_completion)

    def __len__(self):
        """Return the number of constant and function declarations in the model
        `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, f(x) != x)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> len(m)
        2
        """
        return len(self.decls())

    def __getitem__(self, idx):
        """If `idx` is an integer,
        then the declaration at position `idx` in the model `self` is returned.
        If `idx` is a declaration, then the actual interpretation is returned.

        The elements can be retrieved using position or the actual declaration.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.decls()
        [f, x]
        >>> len(m)
        2
        >>> m[0]
        f
        >>> m[1]
        x
        >>> m[x]
        1
        """
        if _is_int(idx):
            return self.decls()[idx]
        if isinstance(idx, ExprRef):
            return self.eval(idx)
        if isinstance(idx, SortRef):
            unimplemented()
        if debugging():
            _assert(False, "Integer, SMT declaration, or SMT constant expected")
        return None

    def decls(self):
        """Return a list with all symbols that have an interpretation in the
        model `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.decls()
        [f, x]
        """
        return sorted(self.vars(), key=lambda v: str(v))


def evaluate(t):
    """Evaluates the given term (assuming it is constant!)"""
    s = Solver()
    s.check()
    m = s.model()
    return m[t]


def simplify(a):
    """Simplify the expression `a`.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> simplify(x + 1 + y + x + 1)
    2 + 2*x + y
    """
    if debugging():
        _assert(is_expr(a), "SMT expression expected")
    instance_check(a, ExprRef)
    return _to_expr_ref(a.ctx.solver.simplify(a.ast), a.ctx)
