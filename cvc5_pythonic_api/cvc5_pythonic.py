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

This is its pythonic API that is (as much as possible) Z3-compatible.

Several online tutorials for Z3Py are available at:
http://rise4fun.com/Z3Py/tutorial/guide

Please send feedback, comments and/or corrections on the Issue tracker for
https://github.com/cvc5/cvc5.git. Your comments are very valuable.

Small example:

>>> x = Int('x')
>>> y = Int('y')
>>> s = Solver()
>>> s.add(x > 0)
>>> s.add(x < 2)
>>> s.add(y == x + 1)
>>> s.check()
sat
>>> m = s.model()
>>> m[x]
1
>>> m[y]
2

SMT exceptions:

>>> try:
...   x = BitVec('x', 32)
...   y = Bool('y')
...   # the expression x + y is type incorrect
...   n = x + y
... except SMTException as ex:
...   print("failed: %s" % ex)
failed: sort mismatch


Differences with Z3py:

* Missing features:
  * Patterns
  * Models for uninterpreted sorts
  * Pseudo-boolean counting constraints
    * AtMost, AtLeast, PbLe, PbGe, PbEq
  * HTML integration
  * String, Sequences, Regexes
  * User propagation hooks
  * Special relations:
    * PartialOrder, LinearOrder, TreeOrder, PiecewiseLinearOrder, TransitiveClosure
  * Optimization
  * FiniteDomainSort
  * Fixedpoint API
  * SMT2 file support
* Not missing, but different
  * Options
    * as expected
  * Some pretty printing
"""
from .cvc5_pythonic_printer import *
from fractions import Fraction
from decimal import Decimal
import ctypes
import decimal
import sys
import math
import io
import functools as ft
import operator as op

import cvc5 as pc
from cvc5 import Kind

DEBUG = __debug__


def debugging():
    global DEBUG
    return DEBUG


def _is_int(v):
    """int testing"""
    return isinstance(v, int)


def unimplemented(msg):
    raise SMTException("Unimplemented: {}".format(msg))


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
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        return list(args[0])
    else:
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
        self.reset()

    def __del__(self):
        self.solver = None

    def reset(self):
        """Fully reset the context. This actually destroys the solver object and
        recreates it. **This invalidates all objects created within this context
        and using them will most likely crash.**
        """
        self.solver = pc.Solver()
        self.solver.setOption("produce-models", "true")
        # Map from (name, sort) pairs to constant terms
        self.vars = {}
        # An increasing identifier used to make fresh identifiers
        self.next_fresh_var = 0

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
    """
# Pending multiple solvers
#    >>> c = Context()
#    >>> c == main_ctx()
#    False
#    >>> x2 = Real('x', c)
#    >>> x2.ctx == c
#    True
#    >>> eq(x, x2)
#    False
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
    """
    Returns `ctx` if it is not `None`, and the default context otherwise.

    >>> get_ctx(None) is main_ctx()
    True
    >>> get_ctx(main_ctx()) is main_ctx()
    True
    """
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

    def __str__(self):
        return obj_to_string(self)

    def __repr__(self):
        return obj_to_string(self)

    def __nonzero__(self):
        """ Convert this expression to a python boolean. See __bool__.

        >>> (BoolVal(False) == BoolVal(False)).__nonzero__()
        True
        """
        return self.__bool__()

    def __bool__(self):
        """ Convert this expression to a python boolean.

        Produces
        * the appropriate value for a BoolVal.
        * whether structural equality holds for an EQ-node

        >>> bool(BoolVal(True))
        True
        >>> bool(BoolVal(False))
        False
        >>> bool(BoolVal(False) == BoolVal(False))
        True
        >>> try:
        ...   bool(Int('y'))
        ... except SMTException as ex:
        ...   print("failed: %s" % ex)
        failed: Symbolic expressions cannot be cast to concrete Boolean values.
        """
        if is_true(self):
            return True
        elif is_false(self):
            return False
        elif is_eq(self) and self.num_args() == 2:
            # Special case so that expressions bool(x == y) yield a Python boolean.
            # This is critical because
            # 1) We want x == y to be symbolic AND
            # 2) we want symbolic terms to be hashable
            #   - in Python, hashable objects must support == that returns
            #     something castable to a Python boolean via __bool__.
            return self.arg(0).eq(self.arg(1))
        else:
            raise SMTException(
                "Symbolic expressions cannot be cast to concrete Boolean values."
            )

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
        It can be used for hash-tables and maps.

        >>> BoolVal(True).get_id() == BoolVal(True).get_id()
        True

        """
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

    def __eq__(self, other):
        """Return an SMT expression that represents the constraint `self == other`.

        If `other` is `None`, then this method simply returns `False`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a == b
        a == b
        >>> a is None
        False
        >>> a == None
        False
        """
        if other is None:
            return False
        a, b = _coerce_exprs(self, other)
        c = self.ctx
        return BoolRef(c.solver.mkTerm(Kind.EQUAL, a.as_ast(), b.as_ast()), c)

    def __hash__(self):
        """Hash code."""
        return self.ast.__hash__()

    def __ne__(self, other):
        """Return an SMT expression that represents the constraint `self != other`.

        If `other` is `None`, then this method simply returns `True`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a != b
        a != b
        >>> a is not None
        True
        >>> a != None
        True
        """
        if other is None:
            return True
        a, b = _coerce_exprs(self, other)
        c = self.ctx
        return BoolRef(c.solver.mkTerm(Kind.DISTINCT, a.as_ast(), b.as_ast()), c)

    def decl(self):
        """Return the SMT function declaration associated with an SMT application.

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> eq(t.decl(), f)
        True
        >>> try:
        ...   Int('y').decl()
        ... except SMTException as ex:
        ...   print("failed: %s" % ex)
        failed: Declarations for non-function applications
        """
        if is_app_of(self, Kind.APPLY_UF):
            return _to_expr_ref(list(self.ast)[0], self.ctx)  # type: ignore
        else:
            raise SMTException("Declarations for non-function applications")

    def kind(self):
        """Return the Kind of this term

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> t.kind() == Kind.APPLY_UF
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
        if is_app_of(self, Kind.APPLY_UF):
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
        if is_app_of(self, Kind.APPLY_UF):
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
        if is_app_of(self, Kind.APPLY_UF):
            return [_to_expr_ref(a, self.ctx) for a in list(self.ast)[1:]]  # type: ignore
        else:
            if is_app(self):
                args = list(self.ast)  # type: ignore
                if self.reverse_children:
                    args = reversed(args)
                return [_to_expr_ref(a, self.ctx) for a in args]
            else:
                return []

    def is_int(self):
        """Return `True` if `self` is of the sort Integer.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> x = Real('x')
        >>> x.is_int()
        False
        >>> Set('x', IntSort()).is_int()
        False
        """
        return False


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

    def __str__(self):
        """
        A pretty-printed representation of this sort.

        >>> str(IntSort())
        'Int'
        """
        return obj_to_string(self)

    def __repr__(self):
        """
        A pretty-printed representation of this sort.

        >>> repr(IntSort())
        'Int'
        """
        return obj_to_string(self)

    def __eq__(self, other):
        return self.ast == other.ast

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> IntSort().sexpr()
        'Int'
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

        >>> n1 = IntSort()
        >>> n2 = RealSort()
        >>> n1.hash() == n2.hash()
        False
        """
        return self.as_ast().__hash__()

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`.

        >>> IntSort().subsort(RealSort())
        True
        >>> BoolSort().subsort(RealSort())
        True
        >>> SetSort(BitVecSort(2)).subsort(SetSort(IntSort()))
        False
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

    def is_int(self):
        """
        Subclasses override

        >>> SetSort(IntSort()).is_int()
        False
        """
        return False

    def is_bool(self):
        return False


def _sort(ctx, a):
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
    >>> solve(a == b)
    [a = (as @a0 A), b = (as @a0 A)]
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

    s must be a base Sort.
    """
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
    elif s.isFloatingPoint():
        return FPSortRef(s, ctx)
    elif s.isRoundingMode():
        return FPRMSortRef(s, ctx)
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

    def name(self):
        """Return the name of the function declaration `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> f.name()
        'f'
        >>> isinstance(f.name(), str)
        True
        """
        return str(self.ast)

    def arity(self):
        """Return the number of arguments of a function declaration.
        If `self` is a constant, then `self.arity()` is 0.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.arity()
        2
        """
        return self.ast.getSort().getFunctionArity()

    def domain(self, i):
        """Return the sort of the argument `i` of a function declaration.
        This method assumes that `0 <= i < self.arity()`.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.domain(0)
        Int
        >>> f.domain(1)
        Real
        """
        return _to_sort_ref(self.ast.getSort().getFunctionDomainSorts()[i], self.ctx)

    def range(self):
        """Return the sort of the range of a function declaration.
        For constants, this is the sort of the constant.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.range()
        Bool
        """
        return _to_sort_ref(self.ast.getSort().getFunctionCodomainSort(), self.ctx)

    def __call__(self, *args):
        """Create an SMT application expression using the function `self`,
        and the given arguments.

        The arguments must be SMT expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a SMT
        integer, then the argument is automatically converted into a
        SMT integer.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> x = Int('x')
        >>> y = Real('y')
        >>> f(x, y)
        f(x, y)
        >>> f(x, x)
        f(x, ToReal(x))
        """
        return _higherorder_apply(self, args, Kind.APPLY_UF)


def _higherorder_apply(func, args, kind):
    """Create an SMT application from a FuncDeclRef and a kind of application"""
    args = _get_args(args)
    num = len(args)
    if debugging():
        _assert(
            num == func.arity(),
            "Incorrect number of arguments to %s" % func,
        )
    _args = []
    for i in range(num):
        tmp = func.domain(i).cast(args[i])
        _args.append(tmp.as_ast())
    return _to_expr_ref(
        func.ctx.solver.mkTerm(kind, func.ast, *_args), func.ctx
    )


def is_func_decl(a):
    """Return `True` if `a` is an SMT function declaration.

    >>> f = Function('f', IntSort(), IntSort())
    >>> is_func_decl(f)
    True
    >>> x = Real('x')
    >>> is_func_decl(x)
    False
    """
    return isinstance(a, FuncDeclRef)

def Function(name, *sig):
    """Create a new SMT uninterpreted function with the given sorts.

    >>> f = Function('f', IntSort(), IntSort())
    >>> f(f(0))
    f(f(0))
    """
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 0, "At least two arguments expected")
    arity = len(sig) - 1
    rng = sig[arity]
    if debugging():
        _assert(is_sort(rng), "SMT sort expected")
    ctx = rng.ctx
    sort = ctx.solver.mkFunctionSort([sig[i].ast for i in range(arity)], rng.ast)
    e = ctx.get_var(name, _to_sort_ref(sort, ctx))
    return FuncDeclRef(e, ctx)


def FreshFunction(*sig):
    """Create a new fresh SMT uninterpreted function with the given sorts.

    >>> f = FreshFunction(IntSort(), IntSort())
    >>> x = Int('x')
    >>> solve([f(x) != f(x)])
    no solution
    """
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 0, "At least two arguments expected")
    arity = len(sig) - 1
    rng = sig[arity]
    if debugging():
        _assert(is_sort(rng), "SMT sort expected")
    ctx = rng.ctx
    sort = ctx.solver.mkFunctionSort([sig[i].ast for i in range(arity)], rng.ast)
    name = ctx.next_fresh(sort, "freshfn")
    return Function(name, *sig)


#########################################
#
# Expressions
#
#########################################


def _to_expr_ref(a, ctx, r=None):
    """Construct the correct ExprRef subclass for `a`

    a may be a base Term or a ExprRef.

    Based on the underlying sort of a.

    >>> _to_expr_ref(BoolVal(True), main_ctx())
    True
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
    if ast.getKind() in [Kind.FORALL, Kind.EXISTS, Kind.LAMBDA]:
        return QuantifierRef(ast, ctx, r)
    sort = ast.getSort()
    if sort.isBoolean():
        return BoolRef(ast, ctx, r)
    if sort.isInteger():
        if ast.getKind() == Kind.CONST_RATIONAL:
            return IntNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isReal():
        if ast.getKind() == Kind.CONST_RATIONAL:
            return RatNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isBitVector():
        if ast.getKind() == Kind.CONST_BITVECTOR:
            return BitVecNumRef(ast, ctx, r)
        else:
            return BitVecRef(ast, ctx, r)
    if sort.isFloatingPoint():
        if ast.getKind() == Kind.CONST_FLOATINGPOINT:
            return FPNumRef(a, ctx)
        else:
            return FPRef(a, ctx)
    if sort.isRoundingMode():
        return FPRMRef(a, ctx)
    if sort.isArray():
        return ArrayRef(ast, ctx, r)
    if sort.isSet():
        return SetRef(ast, ctx, r)
    return ExprRef(ast, ctx, r)


def _coerce_expr_merge(s, a):
    """ Return a sort common to the sort `s` and the term `a`'s sort

    >>> a = Int('a')
    >>> b = Real('b')
    >>> _coerce_expr_merge(None, a)
    Int
    >>> _coerce_expr_merge(RealSort(), a)
    Real
    >>> _coerce_expr_merge(IntSort(), b)
    Real
    """
    if is_expr(a):
        s1 = a.sort()
        if s is None:
            return s1
        if s1.eq(s):
            return s
        elif s.subsort(s1):
            return s1
        elif s1.subsort(s):
            return s
        else:
            if debugging():
                _assert(s1.ctx == s.ctx, "context mismatch")
                _assert(False, "sort mismatch")
    else:
        return s


def _coerce_exprs(a, b, ctx=None):
    """ Return a sort common to that of `a` and `b`.

    Used in binary term-maker functions.

    >>> a = Int('a')
    >>> b = Real('b')
    >>> _coerce_exprs(a, b)
    (ToReal(a), b)
    >>> _coerce_exprs(True, False)
    (True, False)
    >>> _coerce_exprs(1.1, 4)
    (11/10, ToReal(4))
    >>> try:
    ...  _coerce_exprs(1.1, {})
    ... except SMTException as e:
    ...  print("failed: %s" % e)
    failed: Python bool, int, long or float expected
    """
    if not is_expr(a) and not is_expr(b):
        a = _py2expr(a, ctx)
        b = _py2expr(b, ctx)
    s = None
    s = _coerce_expr_merge(s, a)
    s = _coerce_expr_merge(s, b)
    a = s.cast(a)
    b = s.cast(b)
    return (a, b)


def _coerce_expr_list(alist, ctx=None):
    """ Return a sort common to all items in the list.

    Used in n-ary term-maker functions.

    >>> a = Int('a')
    >>> b = Real('b')
    >>> _coerce_expr_list([a, b])
    [ToReal(a), b]
    >>> _coerce_expr_list([True, False])
    [True, False]
    """
    assert len(alist) > 0
    has_expr = False
    for a in alist:
        if is_expr(a):
            has_expr = True
            break
    if not has_expr:
        alist = [_py2expr(a, ctx) for a in alist]
    s = ft.reduce(_coerce_expr_merge, alist, None)
    assert s is not None
    return [s.cast(a) for a in alist]


def _nary_kind_builder(kind, *args):
    """ Helper for defining n-ary builders where args can represent a list of
    expressions, either as a python list or tuple, or as a var-arg sequence of
    expressions.

    The args list can also terminate in a context, which will be used if
    present. If missing, then a context will be infered from the other
    arguments.
    """
    last_arg = None
    if len(args) > 0:
        last_arg = args[-1]
    if isinstance(last_arg, Context):
        ctx = args[-1]
        args = args[:-1]
    elif len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        ctx = args[0][0]
        args = list(args[0])
    else:
        ctx = None
    args = _get_args(args)
    ctx = _get_ctx(_ctx_from_ast_arg_list(args, ctx))
    if debugging():
        _assert(
            ctx is not None,
            "At least one of the arguments must be an SMT expression",
        )
    args = _coerce_expr_list(args, ctx)
    return _to_expr_ref(ctx.solver.mkTerm(kind, *[a.ast for a in args]), ctx)


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


def is_const(a):
    """Return `True` if `a` is SMT constant/variable expression.

    These include:
        * concrete (i.e. literal, or non-symbolic) values
        * declared constants
    These do not include:
        * bound variables
        * quantified formulae
        * applied operators

    >>> a = Int('a')
    >>> is_const(a)
    True
    >>> is_const(a + 1)
    False
    >>> is_const(1)
    False
    >>> is_const(IntVal(1))
    True
    >>> x = Int('x')
    """
    return is_expr(a) and a.ast.getKind() in [
        Kind.CONST_BOOLEAN,
        Kind.CONST_BITVECTOR,
        Kind.CONST_FLOATINGPOINT,
        Kind.CONST_RATIONAL,
        Kind.SET_EMPTY,
        Kind.SET_UNIVERSE,
        Kind.CONSTANT,
    ]


def is_var(a):
    """Return `True` if `a` is bound variable.

    >>> x = Int('x')
    >>> is_var(x)
    False
    >>> is_const(x)
    True
    >>> is_var(BoolSort())
    False
    """
    if not is_expr(a):
        return False
    k = a.ast.getKind()
    return k == Kind.VARIABLE


def is_app_of(a, k):
    """Return `True` if `a` is an application of the given kind `k`.

    >>> x = Int('x')
    >>> n = x + 1
    >>> is_app_of(n, Kind.ADD)
    True
    >>> is_app_of(n, Kind.MULT)
    False
    """
    return is_expr(a) and a.ast.getKind() == k


def If(a, b, c, ctx=None):
    """Create an SMT if-then-else expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> max = If(x > y, x, y)
    >>> max
    If(x > y, x, y)
    >>> If(True, 1, 0, main_ctx())
    If(True, 1, 0)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b, c], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b, c = _coerce_exprs(b, c, ctx)
    if debugging():
        _assert(a.ctx == b.ctx, "Context mismatch")
    return _to_expr_ref(ctx.solver.mkTerm(Kind.ITE, a.ast, b.ast, c.ast), ctx)


def Distinct(*args):
    """Create an SMT distinct expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> Distinct(x, y)
    x != y
    >>> z = Int('z')
    >>> Distinct(x, y, z)
    Distinct(x, y, z)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    if debugging():
        _assert(
            ctx is not None, "At least one of the arguments must be an SMT expression"
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(Kind.DISTINCT, *[a.ast for a in args]), ctx)


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
    """Create a fresh constant of a specified sort

    >>> x = FreshConst(BoolSort(), prefix="test")
    >>> y = FreshConst(BoolSort(), prefix="test")
    >>> x.eq(y)
    False
    """
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

    def cast(self, val):
        """Try to cast `val` as a Boolean.

        >>> x = BoolSort().cast(True)
        >>> x
        True
        >>> is_expr(x)
        True
        >>> is_expr(True)
        False
        >>> x.sort()
        Bool
        >>> try:
        ...   BoolSort().cast(Int('y'))
        ... except SMTException as ex:
        ...   print("failed")
        failed
        >>> try:
        ...   BoolSort().cast(1)
        ... except SMTException as ex:
        ...   print("failed")
        failed
        """
        if isinstance(val, bool):
            return BoolVal(val, self.ctx)
        if debugging():
            if not is_expr(val):
                _assert(
                    is_expr(val),
                    "True, False or SMT Boolean expression expected. Received %s of type %s"
                    % (val, type(val)),
                )
            if not self.eq(val.sort()):
                _assert(
                    self.eq(val.sort()),
                    "Value cannot be converted into an SMT Boolean value",
                )
        return val

    def subsort(self, other):
        return isinstance(other, ArithSortRef)

    def is_int(self):
        """Return `True` if `self` is of the sort Integer.

        >>> x = IntSort()
        >>> x.is_int()
        True
        >>> x = RealSort()
        >>> x.is_int()
        False
        >>> x = BoolSort()
        >>> x.is_int()
        True
        """
        return True

    def is_bool(self):
        """Return `True` if `self` is of the sort Boolean.

        >>> x = BoolSort()
        >>> x.is_bool()
        True
        """
        return True


class BoolRef(ExprRef):
    """All Boolean expressions are instances of this class."""

    def sort(self):
        return _sort(self.ctx, self.ast)

    def __rmul__(self, other):
        """
        >>> x = Real("x")
        >>> x * BoolVal(True)
        If(True, x, 0)
        """
        return self * other

    def __mul__(self, other):
        """Create the SMT expression `self * other`.

        >>> x = Real("x")
        >>> BoolVal(True) * x
        If(True, x, 0)
        """
        if other == 1:
            return self
        if other == 0:
            return 0
        return If(self, other, 0)


def is_bool(a):
    """Return `True` if `a` is an SMT Boolean expression.

    >>> p = Bool('p')
    >>> is_bool(p)
    True
    >>> q = Bool('q')
    >>> is_bool(And(p, q))
    True
    >>> x = Real('x')
    >>> is_bool(x)
    False
    >>> is_bool(x == 0)
    True
    """
    return isinstance(a, BoolRef)


def is_true(a):
    """Return `True` if `a` is the SMT true expression.

    >>> p = Bool('p')
    >>> is_true(p)
    False
    >>> x = Real('x')
    >>> is_true(x == 0)
    False
    >>> # True is a Python Boolean expression
    >>> is_true(True)
    False
    """
    return is_app_of(a, Kind.CONST_BOOLEAN) and a.ast == a.ctx.solver.mkTrue()


def is_false(a):
    """Return `True` if `a` is the SMT false expression.

    >>> p = Bool('p')
    >>> is_false(p)
    False
    >>> is_false(False)
    False
    >>> is_false(BoolVal(False))
    True
    """
    return is_app_of(a, Kind.CONST_BOOLEAN) and a.ast == a.ctx.solver.mkFalse()


def is_and(a):
    """Return `True` if `a` is an SMT and expression.

    >>> p, q = Bools('p q')
    >>> is_and(And(p, q))
    True
    >>> is_and(Or(p, q))
    False
    """
    return is_app_of(a, Kind.AND)


def is_or(a):
    """Return `True` if `a` is an SMT or expression.

    >>> p, q = Bools('p q')
    >>> is_or(Or(p, q))
    True
    >>> is_or(And(p, q))
    False
    """
    return is_app_of(a, Kind.OR)


def is_implies(a):
    """Return `True` if `a` is an SMT implication expression.

    >>> p, q = Bools('p q')
    >>> is_implies(Implies(p, q))
    True
    >>> is_implies(And(p, q))
    False
    """
    return is_app_of(a, Kind.IMPLIES)


def is_xor(a):
    """Return `True` if `a` is an SMT XOR expression.

    >>> p, q = Bools('p q')
    >>> is_xor(Xor(p, q))
    True
    >>> is_xor(And(p, q))
    False
    """
    return is_app_of(a, Kind.XOR)


def is_not(a):
    """Return `True` if `a` is an SMT not expression.

    >>> p = Bool('p')
    >>> is_not(p)
    False
    >>> is_not(Not(p))
    True
    """
    return is_app_of(a, Kind.NOT)


def is_eq(a):
    """Return `True` if `a` is an SMT equality expression.

    >>> x, y = Ints('x y')
    >>> is_eq(x == y)
    True
    """
    return is_app_of(a, Kind.EQUAL)


def is_distinct(a):
    """Return `True` if `a` is an SMT distinct expression.

    >>> x, y, z = Ints('x y z')
    >>> is_distinct(x == y)
    False
    >>> is_distinct(Distinct(x, y, z))
    True
    """
    return is_app_of(a, Kind.DISTINCT)


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


def BoolVal(val, ctx=None):
    """Return the Boolean value `True` or `False`. If `ctx=None`, then the
    global context is used.

    >>> BoolVal(True)
    True
    >>> is_true(BoolVal(True))
    True
    >>> is_true(True)
    False
    >>> is_false(BoolVal(False))
    True
    """
    ctx = _get_ctx(ctx)
    if not val:
        return BoolRef(ctx.solver.mkFalse(), ctx)
    else:
        return BoolRef(ctx.solver.mkTrue(), ctx)


def Bool(name, ctx=None):
    """Return a Boolean constant named `name`. If `ctx=None`, then the global context is used.

    >>> p = Bool('p')
    >>> q = Bool('q')
    >>> And(p, q)
    And(p, q)
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, BoolSort(ctx))
    return BoolRef(e, ctx)


def Bools(names, ctx=None):
    """Return a tuple of Boolean constants.

    `names` is a single string containing all names separated by blank spaces.
    If `ctx=None`, then the global context is used.

    >>> p, q, r = Bools('p q r')
    >>> And(p, Or(q, r))
    And(p, Or(q, r))
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Bool(name, ctx) for name in names]


def BoolVector(prefix, sz, ctx=None):
    """Return a list of Boolean constants of size `sz`.

    The constants are named using the given prefix.
    If `ctx=None`, then the global context is used.

    >>> P = BoolVector('p', 3)
    >>> P
    [p__0, p__1, p__2]
    >>> And(P)
    And(p__0, p__1, p__2)
    """
    return [Bool("%s__%s" % (prefix, i)) for i in range(sz)]


def FreshBool(prefix="b", ctx=None):
    """Return a fresh Boolean constant in the given context using the given prefix.

    If `ctx=None`, then the global context is used.

    >>> b1 = FreshBool()
    >>> b2 = FreshBool()
    >>> eq(b1, b2)
    False
    """
    ctx = _get_ctx(ctx)
    sort = BoolSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Bool(name, ctx)


def Implies(a, b, ctx=None):
    """Create an SMT implies expression.

    >>> p, q = Bools('p q')
    >>> Implies(p, q)
    Implies(p, q)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(ctx.solver.mkTerm(Kind.IMPLIES, a.as_ast(), b.as_ast()), ctx)


def Xor(a, b, ctx=None):
    """Create an SMT Xor expression.

    >>> p, q = Bools('p q')
    >>> Xor(p, q)
    Xor(p, q)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(ctx.solver.mkTerm(Kind.XOR, a.as_ast(), b.as_ast()), ctx)


def Not(a, ctx=None):
    """Create an SMT not expression or probe.

    >>> p = Bool('p')
    >>> Not(Not(p))
    Not(Not(p))
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    return BoolRef(ctx.solver.mkTerm(Kind.NOT, a.as_ast()), ctx)


def mk_not(a):
    """ Negate a boolean expression.
    Strips a negation if one is already present

    >>> x = Bool('x')
    >>> mk_not(x)
    Not(x)
    >>> mk_not(mk_not(x))
    x
    """
    if is_not(a):
        return a.arg(0)
    else:
        return Not(a)


def And(*args):
    """Create an SMT and-expression or and-probe.

    >>> p, q, r = Bools('p q r')
    >>> And(p, q, r)
    And(p, q, r)
    >>> And(p, q, r, main_ctx())
    And(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> And(P)
    And(p__0, p__1, p__2, p__3, p__4)
    """
    return _nary_kind_builder(Kind.AND, *args)


def Or(*args):
    """Create an SMT or-expression or or-probe.

    >>> p, q, r = Bools('p q r')
    >>> Or(p, q, r)
    Or(p, q, r)
    >>> Or(p, q, r, main_ctx())
    Or(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> Or(P)
    Or(p__0, p__1, p__2, p__3, p__4)
    """
    return _nary_kind_builder(Kind.OR, *args)


#########################################
#
# Arithmetic
#
#########################################


class ArithSortRef(SortRef):
    """Real and Integer sorts."""

    def is_real(self):
        """Return `True` if `self` is of the sort Real.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        >>> x = Int('x')
        >>> x.is_real()
        False
        """
        return self.ast == self.ctx.solver.getRealSort()

    def is_int(self):
        """Return `True` if `self` is of the sort Integer.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> x = Real('x')
        >>> x.is_int()
        False
        """
        return self.ast == self.ctx.solver.getIntegerSort()

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`."""
        return self.is_int() and isinstance(other, ArithSortRef) and other.is_real()

    def cast(self, val):
        """Try to cast `val` as an Integer or Real.

        >>> IntSort().cast(10)
        10
        >>> is_int(IntSort().cast(10))
        True
        >>> is_int(10)
        False
        >>> RealSort().cast(10)
        10
        >>> is_real(RealSort().cast(10))
        True
        >>> IntSort().cast(Bool('x'))
        If(x, 1, 0)
        >>> RealSort().cast(Bool('x'))
        ToReal(If(x, 1, 0))
        >>> try:
        ...   IntSort().cast(RealVal("1.1"))
        ... except SMTException as ex:
        ...   print("failed")
        failed
        """
        if is_expr(val):
            if debugging():
                _assert(self.ctx == val.ctx, "Context mismatch")
            val_s = val.sort()
            if self.eq(val_s):
                return val
            if val_s.is_bool() and self.is_int():
                return If(val, 1, 0)
            if val_s.is_bool() and self.is_real():
                return ToReal(If(val, 1, 0))
            if val_s.is_int() and self.is_real():
                return ToReal(val)
            if debugging():
                _assert(False, "SMT Integer/Real expression expected")
        else:
            if self.is_int():
                return IntVal(val, self.ctx)
            if self.is_real():
                return RealVal(val, self.ctx)
            if debugging():
                _assert(
                    False,
                    "int, long, float, string (numeral), or SMT Integer/Real expression expected. Got %s"
                    % self,
                )


def is_arith_sort(s):
    """Return `True` if s is an arithmetical sort (type).

    >>> is_arith_sort(IntSort())
    True
    >>> is_arith_sort(RealSort())
    True
    >>> is_arith_sort(BoolSort())
    False
    >>> n = Int('x') + 1
    >>> is_arith_sort(n.sort())
    True
    """
    return isinstance(s, ArithSortRef)


class ArithRef(ExprRef):
    """Integer and Real expressions."""

    def sort(self):
        """Return the sort (type) of the arithmetical expression `self`.

        >>> Int('x').sort()
        Int
        >>> (Real('x') + 1).sort()
        Real
        """
        return _sort(self.ctx, self.ast)

    def is_int(self):
        """Return `True` if `self` is an integer expression.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> y = Real('y')
        >>> (x + y).is_int()
        False
        """
        # safe b/c will always yield an ArithSortRef
        return self.sort().is_int()  # type: ignore

    def is_real(self):
        """Return `True` if `self` is an real expression.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        """
        # safe b/c will always yield an ArithSortRef
        return self.sort().is_real()  # type: ignore

    def __add__(self, other):
        """Create the SMT expression `self + other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x + y
        x + y
        >>> (x + y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.ADD, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the SMT expression `other + self`.

        >>> x = Int('x')
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.ADD, b.ast, a.ast), self.ctx)

    def __mul__(self, other):
        """Create the SMT expression `self * other`.

        >>> x = Real('x')
        >>> y = Real('y')
        >>> x * y
        x*y
        >>> (x * y).sort()
        Real
        >>> x * BoolVal(True)
        If(True, x, 0)
        """
        if isinstance(other, BoolRef):
            return other.__mul__(self)
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.MULT, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the SMT expression `other * self`.

        >>> x = Real('x')
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.MULT, b.ast, a.ast), self.ctx)

    def __sub__(self, other):
        """Create the SMT expression `self - other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x - y
        x - y
        >>> (x - y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.SUB, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the SMT expression `other - self`.

        >>> x = Int('x')
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.SUB, b.ast, a.ast), self.ctx)

    def __pow__(self, other):
        """Create the SMT expression `self**other` (** is the power operator).

        >>> x = Real('x')
        >>> x**3
        x**3
        >>> (x**3).sort()
        Real
        >>> solve([x ** 2 == x, x > 0])
        [x = 1]
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.POW, a.ast, b.ast), self.ctx)

    def __rpow__(self, other):
        """Create the SMT expression `other**self` (** is the power operator).

        >>> x = Real('x')
        >>> 2**x
        2**x
        >>> (2**x).sort()
        Real
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(Kind.POW, b.ast, a.ast), self.ctx)

    def __div__(self, other):
        """Create the SMT expression `other/self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Int
        >>> (x/y).sexpr()
        '(div x y)'
        >>> x = Real('x')
        >>> y = Real('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Real
        >>> (x/y).sexpr()
        '(/ x y)'
        """
        a, b = _coerce_exprs(self, other)
        if a.sort() == IntSort(self.ctx):
            k = Kind.INTS_DIVISION
        else:
            k = Kind.DIVISION
        return ArithRef(a.ctx.solver.mkTerm(k, a.ast, b.ast), self.ctx)

    def __truediv__(self, other):
        """Create the SMT expression `other/self`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the SMT expression `other/self`.

        >>> x = Int('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(div 10 x)'
        >>> x = Real('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(/ 10.0 x)'
        """
        a, b = _coerce_exprs(self, other)
        if a.sort() == IntSort(self.ctx):
            k = Kind.INTS_DIVISION
        else:
            k = Kind.DIVISION
        return ArithRef(a.ctx.solver.mkTerm(k, b.ast, a.ast), self.ctx)

    def __rtruediv__(self, other):
        """Create the SMT expression `other/self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the SMT expression `other%self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x % y
        x%y
        """
        a, b = _coerce_exprs(self, other)
        if debugging():
            _assert(a.sort().is_int(), "SMT integer expression expected")
        return ArithRef(a.ctx.solver.mkTerm(Kind.INTS_MODULUS, a.ast, b.ast), self.ctx)

    def __rmod__(self, other):
        """Create the SMT expression `other%self`.

        >>> x = Int('x')
        >>> 10 % x
        10%x
        """
        a, b = _coerce_exprs(self, other)
        if debugging():
            _assert(a.sort().is_int(), "SMT integer expression expected")
        return ArithRef(a.ctx.solver.mkTerm(Kind.INTS_MODULUS, b.ast, a.ast), self.ctx)

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = Int('x')
        >>> -x
        -x
        """
        return ArithRef(self.ctx.solver.mkTerm(Kind.NEG, self.ast), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = Int('x')
        >>> +x
        x
        """
        return self

    def __le__(self, other):
        """Create the SMT expression `other <= self`.

        >>> x, y = Ints('x y')
        >>> x <= y
        x <= y
        >>> y = Real('y')
        >>> x <= y
        ToReal(x) <= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(Kind.LEQ, a.ast, b.ast), self.ctx)

    def __lt__(self, other):
        """Create the SMT expression `other < self`.

        >>> x, y = Ints('x y')
        >>> x < y
        x < y
        >>> y = Real('y')
        >>> x < y
        ToReal(x) < y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(Kind.LT, a.ast, b.ast), self.ctx)

    def __gt__(self, other):
        """Create the SMT expression `other > self`.

        >>> x, y = Ints('x y')
        >>> x > y
        x > y
        >>> y = Real('y')
        >>> x > y
        ToReal(x) > y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(Kind.GT, a.ast, b.ast), self.ctx)

    def __ge__(self, other):
        """Create the SMT expression `other >= self`.

        >>> x, y = Ints('x y')
        >>> x >= y
        x >= y
        >>> y = Real('y')
        >>> x >= y
        ToReal(x) >= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(Kind.GEQ, a.ast, b.ast), self.ctx)


def is_arith(a):
    """Return `True` if `a` is an arithmetical expression.

    >>> x = Int('x')
    >>> is_arith(x)
    True
    >>> is_arith(x + 1)
    True
    >>> is_arith(1)
    False
    >>> is_arith(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_arith(y)
    True
    >>> is_arith(y + 1)
    True
    """
    return isinstance(a, ArithRef)


def is_int(a):
    """Return `True` if `a` is an integer expression.

    >>> x = Int('x')
    >>> is_int(x + 1)
    True
    >>> is_int(1)
    False
    >>> is_int(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_int(y)
    False
    >>> is_int(y + 1)
    False
    """
    return is_arith(a) and a.is_int()


def is_real(a):
    """Return `True` if `a` is a real expression.

    >>> x = Int('x')
    >>> is_real(x + 1)
    False
    >>> y = Real('y')
    >>> is_real(y)
    True
    >>> is_real(y + 1)
    True
    >>> is_real(1)
    False
    >>> is_real(RealVal(1))
    True
    """
    return is_arith(a) and a.is_real()


def _is_numeral(ctx, term):
    return term.getKind() in [Kind.CONST_RATIONAL, Kind.CONST_BITVECTOR, Kind.CONST_BOOLEAN, Kind.CONST_ROUNDINGMODE, Kind.CONST_FLOATINGPOINT]


def is_int_value(a):
    """Return `True` if `a` is an integer value of sort Int.

    >>> is_int_value(IntVal(1))
    True
    >>> is_int_value(1)
    False
    >>> is_int_value(Int('x'))
    False
    >>> n = Int('x') + 1
    >>> n
    x + 1
    >>> n.arg(1)
    1
    >>> is_int_value(n.arg(1))
    True
    >>> is_int_value(RealVal("1/3"))
    False
    >>> is_int_value(RealVal(1))
    False
    """
    return is_arith(a) and a.is_int() and _is_numeral(a.ctx, a.as_ast())


def is_rational_value(a):
    """Return `True` if `a` is rational value of sort Real.

    >>> is_rational_value(RealVal(1))
    True
    >>> is_rational_value(RealVal("3/5"))
    True
    >>> is_rational_value(IntVal(1))
    False
    >>> is_rational_value(1)
    False
    >>> n = Real('x') + 1
    >>> n.arg(1)
    1
    >>> is_rational_value(n.arg(1))
    True
    >>> is_rational_value(Real('x'))
    False
    """
    return is_arith(a) and a.is_real() and _is_numeral(a.ctx, a.as_ast())


def is_bool_value(a):
    """Return `True` if `a` is an integer value of sort Int.

    >>> is_bool_value(IntVal(1))
    False
    >>> is_bool_value(Bool('x'))
    False
    >>> is_bool_value(BoolVal(False))
    True
    """
    return is_bool(a) and _is_numeral(a.ctx, a.as_ast())


def is_add(a):
    """Return `True` if `a` is an expression of the form b + c.

    >>> x, y = Ints('x y')
    >>> is_add(x + y)
    True
    >>> is_add(x - y)
    False
    """
    return is_app_of(a, Kind.ADD)


def is_mul(a):
    """Return `True` if `a` is an expression of the form b * c.

    >>> x, y = Ints('x y')
    >>> is_mul(x * y)
    True
    >>> is_mul(x - y)
    False
    """
    return is_app_of(a, Kind.MULT)


def is_sub(a):
    """Return `True` if `a` is an expression of the form b - c.

    >>> x, y = Ints('x y')
    >>> is_sub(x - y)
    True
    >>> is_sub(x + y)
    False
    """
    return is_app_of(a, Kind.SUB)


def is_div(a):
    """Return `True` if `a` is a rational division term (i.e. b / c).

    Note: this returns false for integer division. See `is_idiv`.

    >>> x, y = Reals('x y')
    >>> is_div(x / y)
    True
    >>> is_div(x + y)
    False
    >>> x, y = Ints('x y')
    >>> is_div(x / y)
    False
    >>> is_idiv(x / y)
    True
    """
    return is_app_of(a, Kind.DIVISION)


def is_idiv(a):
    """Return `True` if `a` is an expression of the form b div c.

    >>> x, y = Ints('x y')
    >>> is_idiv(x / y)
    True
    >>> is_idiv(x + y)
    False
    """
    return is_app_of(a, Kind.INTS_DIVISION)


def is_mod(a):
    """Return `True` if `a` is an expression of the form b % c.

    >>> x, y = Ints('x y')
    >>> is_mod(x % y)
    True
    >>> is_mod(x + y)
    False
    """
    return is_app_of(a, Kind.INTS_MODULUS)


def is_le(a):
    """Return `True` if `a` is an expression of the form b <= c.

    >>> x, y = Ints('x y')
    >>> is_le(x <= y)
    True
    >>> is_le(x < y)
    False
    """
    return is_app_of(a, Kind.LEQ)


def is_lt(a):
    """Return `True` if `a` is an expression of the form b < c.

    >>> x, y = Ints('x y')
    >>> is_lt(x < y)
    True
    >>> is_lt(x == y)
    False
    """
    return is_app_of(a, Kind.LT)


def is_ge(a):
    """Return `True` if `a` is an expression of the form b >= c.

    >>> x, y = Ints('x y')
    >>> is_ge(x >= y)
    True
    >>> is_ge(x == y)
    False
    """
    return is_app_of(a, Kind.GEQ)


def is_gt(a):
    """Return `True` if `a` is an expression of the form b > c.

    >>> x, y = Ints('x y')
    >>> is_gt(x > y)
    True
    >>> is_gt(x == y)
    False
    """
    return is_app_of(a, Kind.GT)


def is_is_int(a):
    """Return `True` if `a` is an expression of the form IsInt(b).

    >>> x = Real('x')
    >>> is_is_int(IsInt(x))
    True
    >>> is_is_int(x)
    False
    """
    return is_app_of(a, Kind.IS_INTEGER)


def is_to_real(a):
    """Return `True` if `a` is an expression of the form ToReal(b).

    >>> x = Int('x')
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> is_to_real(n)
    True
    >>> is_to_real(x)
    False
    """
    return is_app_of(a, Kind.TO_REAL)


def is_to_int(a):
    """Return `True` if `a` is an expression of the form ToInt(b).

    >>> x = Real('x')
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> is_to_int(n)
    True
    >>> is_to_int(x)
    False
    """
    return is_app_of(a, Kind.TO_INTEGER)


class IntNumRef(ArithRef):
    """Integer values."""

    def as_long(self):
        """Return an SMT integer numeral as a Python long (bignum) numeral.

        >>> v = IntVal(1)
        >>> v + 1
        1 + 1
        >>> v.as_long() + 1
        2
        """
        if debugging():
            _assert(self.is_int(), "Integer value expected")
        return int(self.as_string())

    def as_string(self):
        """Return an SMT integer numeral as a Python string.
        >>> v = IntVal(100)
        >>> v.as_string()
        '100'
        """
        return str(self.ast.toPythonObj())

    def as_binary_string(self):
        """Return an SMT integer numeral as a Python binary string.
        >>> v = IntVal(10)
        >>> v.as_binary_string()
        '1010'
        """
        return "{:b}".format(int(self.as_string()))


class RatNumRef(ArithRef):
    """Rational values."""

    def numerator(self):
        """Return the numerator of an SMT rational numeral.

        >>> is_rational_value(RealVal("3/5"))
        True
        >>> n = RealVal("3/5")
        >>> n.numerator()
        3
        >>> is_rational_value(Q(3,5))
        True
        >>> Q(3,5).numerator()
        3
        """
        return self.as_fraction().numerator

    def denominator(self):
        """Return the denominator of an SMT rational numeral.

        >>> is_rational_value(Q(3,5))
        True
        >>> n = Q(3,5)
        >>> n.denominator()
        5
        """
        return self.as_fraction().denominator

    def numerator_as_long(self):
        """Return the numerator as a Python long.

        >>> v = RealVal(10000000000)
        >>> v
        10000000000
        >>> v + 1
        10000000000 + 1
        >>> v.numerator_as_long() + 1 == 10000000001
        True
        """
        return self.as_fraction().numerator

    def denominator_as_long(self):
        """Return the denominator as a Python long.

        >>> v = RealVal("1/3")
        >>> v
        1/3
        >>> v.denominator_as_long()
        3
        """
        return self.as_fraction().denominator

    def is_int(self):
        return False

    def is_real(self):
        return True

    def is_int_value(self):
        """ Is this arithmetic value an integer?
        >>> RealVal("2/1").is_int_value()
        True
        >>> RealVal("2/3").is_int_value()
        False
        """
        return self.denominator_as_long() == 1

    def as_long(self):
        """ Is this arithmetic value an integer?
        >>> RealVal("2/1").as_long()
        2
        >>> try:
        ...  RealVal("2/3").as_long()
        ... except SMTException as e:
        ...  print("failed: %s" % e)
        failed: Expected integer fraction
        """
        _assert(self.is_int_value(), "Expected integer fraction")
        return self.numerator_as_long()

    def as_decimal(self, prec):
        """Return an SMT rational value as a string in decimal notation using at most `prec` decimal places.

        >>> v = RealVal("1/5")
        >>> v.as_decimal(3)
        '0.2'
        >>> v = RealVal("1/3")
        >>> v.as_decimal(3)
        '0.333'
        """
        f = self.as_fraction()
        decimal.getcontext().prec = prec
        return str(Decimal(f.numerator) / Decimal(f.denominator))

    def as_string(self):
        """Return an SMT rational numeral as a Python string.

        >>> v = Q(3,6)
        >>> v.as_string()
        '1/2'
        """
        r = self.as_fraction()
        if r.denominator == 1:
            return "{}".format(r.numerator)
        else:
            return "{}/{}".format(r.numerator, r.denominator)

    def as_fraction(self):
        """Return an SMT rational as a Python Fraction object.

        >>> v = RealVal("1/5")
        >>> v.as_fraction()
        Fraction(1, 5)
        """
        return self.ast.toPythonObj()


def _py2expr(a, ctx=None):
    if isinstance(a, bool):
        return BoolVal(a, ctx)
    if _is_int(a):
        return IntVal(a, ctx)
    if isinstance(a, float):
        return RealVal(a, ctx)
    if is_expr(a):
        return a
    if debugging():
        _assert(False, "Python bool, int, long or float expected")


def _to_int_str(val):
    if isinstance(val, float):
        return str(int(val))
    elif isinstance(val, bool):
        if val:
            return "1"
        else:
            return "0"
    elif _is_int(val):
        return str(val)
    elif isinstance(val, str):
        return val
    if debugging():
        _assert(False, "Python value cannot be used as an SMT integer")


def IntVal(val, ctx=None):
    """Return an SMT integer value. If `ctx=None`, then the global context is used.

    >>> IntVal(1)
    1
    >>> IntVal("100")
    100
    """
    ctx = _get_ctx(ctx)
    return IntNumRef(ctx.solver.mkInteger(_to_int_str(val)), ctx)


def RealVal(val, ctx=None):
    """Return an SMT real value.

    `val` may be a Python int, long, float or string representing a number in decimal or rational notation.
    If `ctx=None`, then the global context is used.

    >>> RealVal(1)
    1
    >>> RealVal(1).sort()
    Real
    >>> RealVal("3/5")
    3/5
    >>> RealVal("1.5")
    3/2
    """
    ctx = _get_ctx(ctx)
    return RatNumRef(ctx.solver.mkReal(str(val)), ctx)


def RatVal(a, b, ctx=None):
    """Return an SMT rational a/b.

    If `ctx=None`, then the global context is used.

    >>> RatVal(3,5)
    3/5
    >>> RatVal(3,5).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    if debugging():
        _assert(
            _is_int(a) or isinstance(a, str),
            "First argument cannot be converted into an integer",
        )
        _assert(
            _is_int(b) or isinstance(b, str),
            "Second argument cannot be converted into an integer",
        )
    return RatNumRef(ctx.solver.mkReal(a, b), ctx)


def Q(a, b, ctx=None):
    """Return an SMT rational a/b.

    If `ctx=None`, then the global context is used.

    >>> Q(3,5)
    3/5
    >>> Q(3,5).sort()
    Real
    >>> Q(4,8)
    1/2
    """
    return RatVal(a, b)


def ToReal(a):
    """Return the SMT expression ToReal(a).

    >>> x = Int('x')
    >>> x.sort()
    Int
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> n.sort()
    Real
    """
    if debugging():
        _assert(a.is_int(), "SMT integer expression expected.")
    ctx = a.ctx
    return ArithRef(ctx.solver.mkTerm(Kind.TO_REAL, a.ast), ctx)


def ToInt(a):
    """Return the SMT expression ToInt(a).

    >>> x = Real('x')
    >>> x.sort()
    Real
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> n.sort()
    Int
    """
    if debugging():
        _assert(a.is_real(), "SMT real expression expected.")
    ctx = a.ctx
    return ArithRef(ctx.solver.mkTerm(Kind.TO_INTEGER, a.ast), ctx)


def IntSort(ctx=None):
    """Return the integer sort in the given context. If `ctx=None`, then the global context is used.

    >>> IntSort()
    Int
    >>> x = Const('x', IntSort())
    >>> is_int(x)
    True
    >>> x.sort() == IntSort()
    True
    >>> x.sort() == BoolSort()
    False
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(ctx.solver.getIntegerSort(), ctx)


def RealSort(ctx=None):
    """Return the real sort in the given context. If `ctx=None`, then the global context is used.

    >>> RealSort()
    Real
    >>> x = Const('x', RealSort())
    >>> is_real(x)
    True
    >>> is_int(x)
    False
    >>> x.sort() == RealSort()
    True
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(ctx.solver.getRealSort(), ctx)


def Int(name, ctx=None):
    """Return an integer constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Int('x')
    >>> is_int(x)
    True
    >>> is_int(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, IntSort(ctx))
    return ArithRef(e, ctx)


def Ints(names, ctx=None):
    """Return a tuple of Integer constants.

    >>> x, y, z = Ints('x y z')
    >>> Sum(x, y, z)
    x + y + z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Int(name, ctx) for name in names]


def IntVector(prefix, sz, ctx=None):
    """Return a list of integer constants of size `sz`.

    >>> X = IntVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    """
    ctx = _get_ctx(ctx)
    return [Int("%s__%s" % (prefix, i), ctx) for i in range(sz)]


def FreshInt(prefix="x", ctx=None):
    """Return a fresh integer constant in the given context using the given prefix.

    >>> x = FreshInt()
    >>> y = FreshInt()
    >>> eq(x, y)
    False
    >>> x.sort()
    Int
    """
    ctx = _get_ctx(ctx)
    sort = IntSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Int(name, ctx)


def Real(name, ctx=None):
    """Return a real constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Real('x')
    >>> is_real(x)
    True
    >>> is_real(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, RealSort(ctx))
    return ArithRef(e, ctx)


def Reals(names, ctx=None):
    """Return a tuple of real constants.

    >>> x, y, z = Reals('x y z')
    >>> Sum(x, y, z)
    x + y + z
    >>> Sum(x, y, z).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Real(name, ctx) for name in names]


def RealVector(prefix, sz, ctx=None):
    """Return a list of real constants of size `sz`.

    >>> X = RealVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    >>> Sum(X).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    return [Real("%s__%s" % (prefix, i), ctx) for i in range(sz)]


def FreshReal(prefix="b", ctx=None):
    """Return a fresh real constant in the given context using the given prefix.

    >>> x = FreshReal()
    >>> y = FreshReal()
    >>> eq(x, y)
    False
    >>> x.sort()
    Real
    """
    ctx = _get_ctx(ctx)
    sort = RealSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Real(name, ctx)


def IsInt(a):
    """Return the SMT predicate IsInt(a).

    >>> x = Real('x')
    >>> IsInt(x + "1/2")
    IsInt(x + 1/2)
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1)
    [x = 1/2]
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1, x != "1/2")
    no solution
    """
    if debugging():
        _assert(a.is_real(), "SMT real expression expected.")
    ctx = a.ctx
    return BoolRef(ctx.solver.mkTerm(Kind.IS_INTEGER, a.ast), ctx)


def Sqrt(a, ctx=None):
    """Return an SMT expression which represents the square root of a.

    Can also operate on python builtins of arithemtic type.

    >>> x = Real('x')
    >>> Sqrt(x)
    x**(1/2)
    >>> Sqrt(4)
    4**(1/2)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/2"


def Cbrt(a, ctx=None):
    """Return an SMT expression which represents the cubic root of a.

    Can also operate on python builtins of arithemtic type.

    >>> x = Real('x')
    >>> Cbrt(x)
    x**(1/3)
    >>> Cbrt(4)
    4**(1/3)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/3"


def Plus(*args):
    """ Create an SMT addition.

    Deprecated. Kept for compatiblity with Z3. See "Add".

    See also the __add__ overload (+ operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Plus(x, x, y)
    x + x + y
    >>> Plus(x, x, y, main_ctx())
    x + x + y
    """
    return Add(*args)


def Add(*args):
    """ Create an SMT addition.

    See also the __add__ overload (+ operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Add(x, x, y)
    x + x + y
    >>> Add(x, x, y, main_ctx())
    x + x + y
    """
    return _nary_kind_builder(Kind.ADD, *args)


def Mult(*args):
    """ Create an SMT multiplication.

    See also the __mul__ overload (* operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Mult(x, x, y)
    x*x*y
    >>> Mult(x, x, y, main_ctx())
    x*x*y
    """
    return _nary_kind_builder(Kind.MULT, *args)


def Sub(a, b):
    """ Create an SMT subtraction.

    See also the __sub__ overload (- operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Sub(x, y)
    x - y
    """
    return a - b


def Neg(a):
    """ Create an SMT unary negation.

    See also the __neg__ overload (unary - operator) for arithmetic SMT expressions.

    >>> x = Int('x')
    >>> Neg(x)
    -x
    """
    return -a


def UMinus(a):
    """ Create an SMT unary negation.

    Deprecated. Kept for compatiblity with Z3. See "Neg".

    See also the __neg__ overload (unary - operator) for arithmetic SMT expressions.

    >>> x = Int('x')
    >>> UMinus(x)
    -x
    """
    return -a


def Div(a, b):
    """ Create an SMT division.

    See also the __div__ overload (/ operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> a, b = Reals('x y')
    >>> Div(x, y).sexpr()
    '(div x y)'
    >>> Div(a, y).sexpr()
    '(/ x (to_real y))'
    >>> Div(a, b).sexpr()
    '(/ x y)'
    """
    return a / b


def Pow(a, b):
    """ Create an SMT power.

    See also the __pow__ overload for arithmetic SMT expressions.

    >>> x = Int('x')
    >>> Pow(x, 3)
    x**3
    """
    return a ** b


def IntsModulus(a, b):
    """ Create an SMT integer modulus.

    See also the __mod__ overload (% operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> IntsModulus(x, y)
    x%y
    """
    return a % b


def Leq(a, b):
    """ Create an SMT less-than-or-equal-to.

    See also the __le__ overload (<= operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Leq(x, y)
    x <= y
    """
    return a <= b


def Geq(a, b):
    """ Create an SMT greater-than-or-equal-to.

    See also the __ge__ overload (>= operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Geq(x, y)
    x >= y
    """
    return a >= b


def Lt(a, b):
    """ Create an SMT less-than.

    See also the __lt__ overload (< operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Lt(x, y)
    x < y
    """
    return a < b


def Gt(a, b):
    """ Create an SMT greater-than.

    See also the __gt__ overload (> operator) for arithmetic SMT expressions.

    >>> x, y = Ints('x y')
    >>> Gt(x, y)
    x > y
    """
    return a > b


#########################################
#
# Transcendentals
#
#########################################


def Pi(ctx=None):
    """ Create the constant pi

    >>> Pi()
    Pi
    """
    ctx = get_ctx(ctx)
    return _to_expr_ref(ctx.solver.mkTerm(Kind.PI), ctx)


def Exponential(x):
    """ Create an exponential function

    >>> x = Real('x')
    >>> solve(Exponential(x) == 1)
    [x = 0]
    """
    return _nary_kind_builder(Kind.EXPONENTIAL, RealSort().cast(x))


def Sine(x):
    """ Create a sine function

    >>> x = Real('x')
    >>> i = Int('i')
    >>> prove(Sine(x) < 2)
    proved
    >>> prove(Sine(i) < 2)
    proved
    """
    return _nary_kind_builder(Kind.SINE, RealSort().cast(x))


def Cosine(x):
    """ Create a cosine function

    >>> x = Real('x')
    >>> i = Int('i')
    >>> prove(Cosine(x) < 2)
    proved
    >>> prove(Cosine(i) < 2)
    proved
    """
    return _nary_kind_builder(Kind.COSINE, RealSort().cast(x))


def Tangent(x):
    """ Create a tangent function

    >>> Tangent(Real('x'))
    Tangent(x)
    """
    return _nary_kind_builder(Kind.TANGENT, RealSort().cast(x))


def Arcsine(x):
    """ Create an arcsine function

    >>> Arcsine(Real('x'))
    Arcsine(x)
    """
    return _nary_kind_builder(Kind.ARCSINE, RealSort().cast(x))


def Arccosine(x):
    """ Create an arccosine function

    >>> Arccosine(Real('x'))
    Arccosine(x)
    """
    return _nary_kind_builder(Kind.ARCCOSINE, RealSort().cast(x))


def Arctangent(x):
    """ Create an arctangent function

    >>> Arctangent(Real('x'))
    Arctangent(x)
    """
    return _nary_kind_builder(Kind.ARCTANGENT, RealSort().cast(x))


def Secant(x):
    """ Create a secant function

    >>> Secant(Real('x'))
    Secant(x)
    """
    return _nary_kind_builder(Kind.SECANT, RealSort().cast(x))


def Cosecant(x):
    """ Create a cosecant function

    >>> Cosecant(Real('x'))
    Cosecant(x)
    """
    return _nary_kind_builder(Kind.COSECANT, RealSort().cast(x))


def Cotangent(x):
    """ Create a cotangent function

    >>> Cotangent(Real('x'))
    Cotangent(x)
    """
    return _nary_kind_builder(Kind.COTANGENT, RealSort().cast(x))


def Arcsecant(x):
    """ Create an arcsecant function

    >>> Arcsecant(Real('x'))
    Arcsecant(x)
    """
    return _nary_kind_builder(Kind.ARCSECANT, RealSort().cast(x))


def Arccosecant(x):
    """ Create an arccosecant function

    >>> Arccosecant(Real('x'))
    Arccosecant(x)
    """
    return _nary_kind_builder(Kind.ARCCOSECANT, RealSort().cast(x))


def Arccotangent(x):
    """ Create an arccotangent function

    >>> Arccotangent(Real('x'))
    Arccotangent(x)
    """
    return _nary_kind_builder(Kind.ARCCOTANGENT, RealSort().cast(x))


#########################################
#
# Bit-Vectors
#
#########################################


class BitVecSortRef(SortRef):
    """Bit-vector sort."""

    def size(self):
        """Return the size (number of bits) of the bit-vector sort `self`.

        >>> b = BitVecSort(32)
        >>> b.size()
        32
        """
        return self.ast.getBitVectorSize()

    def subsort(self, other):
        return is_bv_sort(other) and self.size() < other.size()

    def cast(self, val):
        """Try to cast `val` as a Bit-Vector.

        >>> b = BitVecSort(32)
        >>> b.cast(10)
        10
        >>> b.cast(10).sexpr()
        '#b00000000000000000000000000001010'
        """
        if is_expr(val):
            if debugging():
                _assert(self.ctx == val.ctx, "Context mismatch")
            # Idea: use sign_extend if sort of val is a bitvector of smaller size
            return val
        else:
            return BitVecVal(val, self)


def is_bv_sort(s):
    """Return True if `s` is an SMT bit-vector sort.

    >>> is_bv_sort(BitVecSort(32))
    True
    >>> is_bv_sort(IntSort())
    False
    """
    return isinstance(s, BitVecSortRef)


class BitVecRef(ExprRef):
    """Bit-vector expressions."""

    def sort(self):
        """Return the sort of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> x.sort()
        BitVec(32)
        >>> x.sort() == BitVecSort(32)
        True
        """
        return _sort(self.ctx, self.ast)

    def size(self):
        """Return the number of bits of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> (x + 1).size()
        32
        >>> Concat(x, x).size()
        64
        """
        # safe b/c will always yield a BitVecSortRef
        return self.sort().size()  # type: ignore

    def __add__(self, other):
        """Create the SMT expression `self + other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x + y
        x + y
        >>> (x + y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_ADD, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the SMT expression `other + self`.

        >>> x = BitVec('x', 32)
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_ADD, b.ast, a.ast), self.ctx)

    def __mul__(self, other):
        """Create the SMT expression `self * other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x * y
        x*y
        >>> (x * y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_MULT, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the SMT expression `other * self`.

        >>> x = BitVec('x', 32)
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_MULT, b.ast, a.ast), self.ctx)

    def __sub__(self, other):
        """Create the SMT expression `self - other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x - y
        x - y
        >>> (x - y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SUB, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the SMT expression `other - self`.

        >>> x = BitVec('x', 32)
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SUB, b.ast, a.ast), self.ctx)

    def __or__(self, other):
        """Create the SMT expression bitwise-or `self | other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x | y
        x | y
        >>> (x | y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_OR, a.ast, b.ast), self.ctx)

    def __ror__(self, other):
        """Create the SMT expression bitwise-or `other | self`.

        >>> x = BitVec('x', 32)
        >>> 10 | x
        10 | x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_OR, b.ast, a.ast), self.ctx)

    def __and__(self, other):
        """Create the SMT expression bitwise-and `self & other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x & y
        x & y
        >>> (x & y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_AND, a.ast, b.ast), self.ctx)

    def __rand__(self, other):
        """Create the SMT expression bitwise-or `other & self`.

        >>> x = BitVec('x', 32)
        >>> 10 & x
        10 & x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_AND, b.ast, a.ast), self.ctx)

    def __xor__(self, other):
        """Create the SMT expression bitwise-xor `self ^ other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x ^ y
        x ^ y
        >>> (x ^ y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_XOR, a.ast, b.ast), self.ctx)

    def __rxor__(self, other):
        """Create the SMT expression bitwise-xor `other ^ self`.

        >>> x = BitVec('x', 32)
        >>> 10 ^ x
        10 ^ x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_XOR, b.ast, a.ast), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = BitVec('x', 32)
        >>> +x
        x
        """
        return self

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = BitVec('x', 32)
        >>> -x
        -x
        >>> solve([-(-x) != x])
        no solution
        """
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_NEG, self.ast), self.ctx)

    def __invert__(self):
        """Create the SMT expression bitwise-not `~self`.

        >>> x = BitVec('x', 32)
        >>> ~x
        ~x
        >>> solve([~(~x) != x])
        no solution
        """
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_NOT, self.ast), self.ctx)

    def __div__(self, other):
        """Create the SMT expression (signed) division `self / other`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x / y
        x/y
        >>> (x / y).sort()
        BitVec(32)
        >>> (x / y).sexpr()
        '(bvsdiv x y)'
        >>> UDiv(x, y).sexpr()
        '(bvudiv x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SDIV, a.ast, b.ast), self.ctx)

    def __truediv__(self, other):
        """Create the SMT expression (signed) division `self / other`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the SMT expression (signed) division `other / self`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> 10 / x
        10/x
        >>> (10 / x).sexpr()
        '(bvsdiv #b00000000000000000000000000001010 x)'
        >>> UDiv(10, x).sexpr()
        '(bvudiv #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SDIV, b.ast, a.ast), self.ctx)

    def __rtruediv__(self, other):
        """Create the SMT expression (signed) division `other / self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the SMT expression (signed) mod `self % other`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x % y
        x%y
        >>> (x % y).sort()
        BitVec(32)
        >>> (x % y).sexpr()
        '(bvsmod x y)'
        >>> URem(x, y).sexpr()
        '(bvurem x y)'
        >>> SRem(x, y).sexpr()
        '(bvsrem x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SMOD, a.ast, b.ast), self.ctx)

    def __rmod__(self, other):
        """Create the SMT expression (signed) mod `other % self`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> 10 % x
        10%x
        >>> (10 % x).sexpr()
        '(bvsmod #b00000000000000000000000000001010 x)'
        >>> URem(10, x).sexpr()
        '(bvurem #b00000000000000000000000000001010 x)'
        >>> SRem(10, x).sexpr()
        '(bvsrem #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SMOD, b.ast, a.ast), self.ctx)

    def __le__(self, other):
        """Create the SMT expression (signed) `other <= self`.

        Use the function ULE() for unsigned less than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x <= y
        x <= y
        >>> (x <= y).sexpr()
        '(bvsle x y)'
        >>> ULE(x, y).sexpr()
        '(bvule x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SLE, a.ast, b.ast), self.ctx)

    def __lt__(self, other):
        """Create the SMT expression (signed) `other < self`.

        Use the function ULT() for unsigned less than.

        >>> x, y = BitVecs('x y', 32)
        >>> x < y
        x < y
        >>> (x < y).sexpr()
        '(bvslt x y)'
        >>> ULT(x, y).sexpr()
        '(bvult x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SLT, a.ast, b.ast), self.ctx)

    def __gt__(self, other):
        """Create the SMT expression (signed) `other > self`.

        Use the function UGT() for unsigned greater than.

        >>> x, y = BitVecs('x y', 32)
        >>> x > y
        x > y
        >>> (x > y).sexpr()
        '(bvsgt x y)'
        >>> UGT(x, y).sexpr()
        '(bvugt x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SGT, a.ast, b.ast), self.ctx)

    def __ge__(self, other):
        """Create the SMT expression (signed) `other >= self`.

        Use the function UGE() for unsigned greater than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x >= y
        x >= y
        >>> (x >= y).sexpr()
        '(bvsge x y)'
        >>> UGE(x, y).sexpr()
        '(bvuge x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SGE, a.ast, b.ast), self.ctx)

    def __rshift__(self, other):
        """Create the SMT expression (arithmetical) right shift `self >> other`

        Use the function LShR() for the right logical shift

        >>> x, y = BitVecs('x y', 32)
        >>> x >> y
        x >> y
        >>> (x >> y).sexpr()
        '(bvashr x y)'
        >>> LShR(x, y).sexpr()
        '(bvlshr x y)'
        >>> BitVecVal(4, 3)
        4
        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> evaluate(BitVecVal(4, 3) >> 1).as_signed_long()
        -2
        >>> evaluate(BitVecVal(4, 3) >> 1)
        6
        >>> evaluate(LShR(BitVecVal(4, 3), 1))
        2
        >>> evaluate(BitVecVal(2, 3) >> 1)
        1
        >>> evaluate(LShR(BitVecVal(2, 3), 1))
        1
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_ASHR, a.ast, b.ast), self.ctx)

    def __lshift__(self, other):
        """Create the SMT expression left shift `self << other`

        >>> x, y = BitVecs('x y', 32)
        >>> x << y
        x << y
        >>> (x << y).sexpr()
        '(bvshl x y)'
        >>> evaluate(BitVecVal(2, 3) << 1)
        4
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SHL, a.ast, b.ast), self.ctx)

    def __rrshift__(self, other):
        """Create the SMT expression (arithmetical) right shift `other` >> `self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 >> x
        10 >> x
        >>> (10 >> x).sexpr()
        '(bvashr #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_ASHR, b.ast, a.ast), self.ctx)

    def __rlshift__(self, other):
        """Create the SMT expression left shift `other << self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 << x
        10 << x
        >>> (10 << x).sexpr()
        '(bvshl #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(Kind.BITVECTOR_SHL, b.ast, a.ast), self.ctx)


class BitVecNumRef(BitVecRef):
    """Bit-vector values."""

    def as_long(self):
        """Return an SMT bit-vector numeral as a Python long (bignum) numeral.

        >>> v = BitVecVal(0xbadc0de, 32)
        >>> v
        195936478
        >>> print("0x%.8x" % v.as_long())
        0x0badc0de
        """
        return int(self.as_binary_string(), 2)

    def as_signed_long(self):
        """Return an SMT bit-vector numeral as a Python long (bignum) numeral.
        The most significant bit is assumed to be the sign.

        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> BitVecVal(7, 3).as_signed_long()
        -1
        >>> BitVecVal(3, 3).as_signed_long()
        3
        >>> BitVecVal(2**32 - 1, 32).as_signed_long()
        -1
        >>> BitVecVal(2**64 - 1, 64).as_signed_long()
        -1
        """
        sz = self.size()
        val = self.as_long()
        if val >= 2 ** (sz - 1):
            val = val - 2 ** sz
        if val < -(2 ** (sz - 1)):
            val = val + 2 ** sz
        return int(val)

    def as_string(self):
        return str(self.as_long())

    def as_binary_string(self):
        return self.ast.getBitVectorValue()


def is_bv(a):
    """Return `True` if `a` is an SMT bit-vector expression.

    >>> b = BitVec('b', 32)
    >>> is_bv(b)
    True
    >>> is_bv(b + 10)
    True
    >>> is_bv(Int('x'))
    False
    """
    return isinstance(a, BitVecRef)


def is_bv_value(a):
    """Return `True` if `a` is an SMT bit-vector numeral value.

    >>> b = BitVec('b', 32)
    >>> is_bv_value(b)
    False
    >>> b = BitVecVal(10, 32)
    >>> b
    10
    >>> is_bv_value(b)
    True
    """
    return is_bv(a) and _is_numeral(a.ctx, a.as_ast())


def BV2Int(a, is_signed=False):
    """Return the SMT expression BV2Int(a).

    >>> b = BitVec('b', 3)
    >>> BV2Int(b).sort()
    Int
    >>> x = Int('x')
    >>> x > BV2Int(b)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=False)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=True)
    x > If(b < 0, BV2Int(b) - 8, BV2Int(b))
    >>> solve(x > BV2Int(b), b == 1, x < 3)
    [b = 1, x = 2]
    """
    if debugging():
        _assert(is_bv(a), "First argument must be an SMT bit-vector expression")
    ctx = a.ctx
    if is_signed:
        w = a.sort().size()
        nat = BV2Int(a)
        return If(a < 0, nat - (2 ** w), nat)
    else:
        return ArithRef(ctx.solver.mkTerm(Kind.BITVECTOR_TO_NAT, a.ast), ctx)


def Int2BV(a, num_bits):
    """Return the SMT expression Int2BV(a, num_bits).
    It is a bit-vector of width num_bits and represents the
    modulo of a by 2^num_bits

    >>> x = Int('x')
    >>> bv_x = Int2BV(x, 2)
    >>> bv_x_plus_4 = Int2BV(x + 4, 2)
    >>> solve([bv_x != bv_x_plus_4])
    no solution
    """
    ctx = a.ctx
    return BitVecRef(ctx.solver.mkTerm(ctx.solver.mkOp(Kind.INT_TO_BITVECTOR, num_bits), a.ast), ctx)


def BitVecSort(sz, ctx=None):
    """Return an SMT bit-vector sort of the given size. If `ctx=None`, then the global context is used.

    >>> Byte = BitVecSort(8)
    >>> Word = BitVecSort(16)
    >>> Byte
    BitVec(8)
    >>> x = Const('x', Byte)
    >>> eq(x, BitVec('x', 8))
    True
    """
    ctx = _get_ctx(ctx)
    return BitVecSortRef(ctx.solver.mkBitVectorSort(sz), ctx)


def BitVecVal(val, bv, ctx=None):
    """Return a bit-vector value with the given number of bits. If `ctx=None`, then the global context is used.
    The second argument can be a number of bits (integer) or a bit-vector sort.

    >>> v = BitVecVal(10, 32)
    >>> v
    10
    >>> print("0x%.8x" % v.as_long())
    0x0000000a
    >>> s = BitVecSort(3)
    >>> u = BitVecVal(10, s)
    >>> u
    2
    """
    if is_bv_sort(bv):
        ctx = bv.ctx
        size = bv.size()
    else:
        size = bv
        ctx = _get_ctx(ctx)
    modulus = 2 ** size
    val = (val + modulus) % modulus
    return BitVecNumRef(ctx.solver.mkBitVector(size, str(val), 10), ctx)


def BitVec(name, bv, ctx=None):
    """Return a bit-vector constant named `name`. `bv` may be the number of bits of a bit-vector sort.
    If `ctx=None`, then the global context is used.

    >>> x  = BitVec('x', 16)
    >>> is_bv(x)
    True
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> word = BitVecSort(16)
    >>> x2 = BitVec('x', word)
    >>> eq(x, x2)
    True
    """
    if isinstance(bv, BitVecSortRef):
        ctx = bv.ctx
    else:
        ctx = _get_ctx(ctx)
        bv = BitVecSort(bv, ctx)
    e = ctx.get_var(name, bv)
    return BitVecRef(e, ctx)


def BitVecs(names, bv, ctx=None):
    """Return a tuple of bit-vector constants of size bv.

    >>> x, y, z = BitVecs('x y z', 16)
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> Sum(x, y, z)
    x + y + z
    >>> Product(x, y, z)
    x*y*z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [BitVec(name, bv, ctx) for name in names]


def Concat(*args):
    """Create an SMT bit-vector concatenation expression.

    >>> v = BitVecVal(1, 4)
    >>> Concat(v, v+1, v)
    Concat(1, 1 + 1, 1)
    >>> evaluate(Concat(v, v+1, v))
    289
    >>> print("%.3x" % simplify(Concat(v, v+1, v)).as_long())
    121
    """
    args = _get_args(args)
    sz = len(args)
    if debugging():
        _assert(sz >= 2, "At least two arguments expected.")

    ctx = None
    for a in args:
        if is_expr(a):
            ctx = a.ctx
            break
    if debugging():
        _assert(
            all([is_bv(a) for a in args]),
            "All arguments must be SMT bit-vector expressions.",
        )
    return BitVecRef(ctx.solver.mkTerm(Kind.BITVECTOR_CONCAT, *[a.ast for a in args]))


def Extract(high, low, a):
    """Create an SMT bit-vector extraction expression, or create a string extraction expression.

    >>> x = BitVec('x', 8)
    >>> Extract(6, 2, x)
    Extract(6, 2, x)
    >>> Extract(6, 2, x).sort()
    BitVec(5)
    """
    if debugging():
        _assert(
            low <= high,
            "First argument must be greater than or equal to second argument",
        )
        _assert(
            _is_int(high) and high >= 0 and _is_int(low) and low >= 0,
            "First and second arguments must be non negative integers",
        )
        _assert(is_bv(a), "Third argument must be an SMT bit-vector expression")
    return BitVecRef(
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(Kind.BITVECTOR_EXTRACT, high, low), a.ast), a.ctx
    )


def _check_bv_args(a, b):
    if debugging():
        _assert(
            is_bv(a) or is_bv(b),
            "First or second argument must be an SMT bit-vector expression",
        )


def ULE(a, b):
    """Create the SMT expression (unsigned) `other <= self`.

    Use the operator <= for signed less than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> ULE(x, y)
    ULE(x, y)
    >>> (x <= y).sexpr()
    '(bvsle x y)'
    >>> ULE(x, y).sexpr()
    '(bvule x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_ULE, a.ast, b.ast), a.ctx)


def ULT(a, b):
    """Create the SMT expression (unsigned) `other < self`.

    Use the operator < for signed less than.

    >>> x, y = BitVecs('x y', 32)
    >>> ULT(x, y)
    ULT(x, y)
    >>> (x < y).sexpr()
    '(bvslt x y)'
    >>> ULT(x, y).sexpr()
    '(bvult x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_ULT, a.ast, b.ast), a.ctx)


def UGE(a, b):
    """Create the SMT expression (unsigned) `other >= self`.

    Use the operator >= for signed greater than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> UGE(x, y)
    UGE(x, y)
    >>> (x >= y).sexpr()
    '(bvsge x y)'
    >>> UGE(x, y).sexpr()
    '(bvuge x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_UGE, a.ast, b.ast), a.ctx)


def UGT(a, b):
    """Create the SMT expression (unsigned) `other > self`.

    Use the operator > for signed greater than.

    >>> x, y = BitVecs('x y', 32)
    >>> UGT(x, y)
    UGT(x, y)
    >>> (x > y).sexpr()
    '(bvsgt x y)'
    >>> UGT(x, y).sexpr()
    '(bvugt x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_UGT, a.ast, b.ast), a.ctx)


def SLE(a, b):
    """Create the SMT expression (signed) `other <= self`.

    See also the __le__ overload (<= operator) for BitVecRef

    >>> x, y = BitVecs('x y', 32)
    >>> SLE(x, y).sexpr()
    '(bvsle x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_SLE, a.ast, b.ast), a.ctx)


def SLT(a, b):
    """Create the SMT expression (signed) `other < self`.

    See also the __lt__ overload (< operator) for BitVecRef

    >>> x, y = BitVecs('x y', 32)
    >>> SLT(x, y).sexpr()
    '(bvslt x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_SLT, a.ast, b.ast), a.ctx)


def SGE(a, b):
    """Create the SMT expression (signed) `other >= self`.

    See also the __ge__ overload (>= operator) for BitVecRef

    >>> x, y = BitVecs('x y', 32)
    >>> SGE(x, y).sexpr()
    '(bvsge x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_SGE, a.ast, b.ast), a.ctx)


def SGT(a, b):
    """Create the SMT expression (signed) `other > self`.

    See also the __gt__ overload (> operator) for BitVecRef

    >>> x, y = BitVecs('x y', 32)
    >>> SGT(x, y).sexpr()
    '(bvsgt x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_SGT, a.ast, b.ast), a.ctx)


def UDiv(a, b):
    """Create the SMT expression (unsigned) division `self / other`.

    Use the operator / for signed division.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> UDiv(x, y)
    UDiv(x, y)
    >>> UDiv(x, y).sort()
    BitVec(32)
    >>> (x / y).sexpr()
    '(bvsdiv x y)'
    >>> UDiv(x, y).sexpr()
    '(bvudiv x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_UDIV, a.ast, b.ast), a.ctx)


def URem(a, b):
    """Create the SMT expression (unsigned) remainder `self % other`.

    Use the operator % for signed modulus, and SRem() for signed remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> URem(x, y)
    URem(x, y)
    >>> URem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> URem(x, y).sexpr()
    '(bvurem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_UREM, a.ast, b.ast), a.ctx)


def SDiv(a, b):
    """Create an SMT signed division expression.

    See also the __div__ overload (/ operator) for BitVecRef.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> SDiv(x, y)
    x/y
    """
    return a / b


def SMod(a, b):
    """Create an SMT expression for the signed modulus `self % other`.

    See also the __mod__ overload (% operator) for BitVecRef.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> SMod(x, y)
    x%y
    """
    return a % b


def SRem(a, b):
    """Create the SMT expression signed remainder.

    Use the operator % for signed modulus, and URem() for unsigned remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> SRem(x, y)
    SRem(x, y)
    >>> SRem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> SRem(x, y).sexpr()
    '(bvsrem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_SREM, a.ast, b.ast), a.ctx)


def LShR(a, b):
    """Create the SMT expression logical right shift.

    Use the operator >> for the arithmetical right shift.

    >>> x, y = BitVecs('x y', 32)
    >>> LShR(x, y)
    LShR(x, y)
    >>> (x >> y).sexpr()
    '(bvashr x y)'
    >>> LShR(x, y).sexpr()
    '(bvlshr x y)'
    >>> BitVecVal(4, 3)
    4
    >>> BitVecVal(4, 3).as_signed_long()
    -4
    >>> simplify(BitVecVal(4, 3) >> 1).as_signed_long()
    -2
    >>> simplify(BitVecVal(4, 3) >> 1)
    6
    >>> simplify(LShR(BitVecVal(4, 3), 1))
    2
    >>> simplify(BitVecVal(2, 3) >> 1)
    1
    >>> simplify(LShR(BitVecVal(2, 3), 1))
    1
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_LSHR, a.ast, b.ast), a.ctx)


def _check_rotate_args(a, b):
    if debugging():
        _assert(isinstance(b, int), "Can only rotate by an integer")
        _assert(b >= 0, "Can't rotate by a negative amount")
        _assert(is_bv(a), "Can only rotate a bit-vector")


def RotateLeft(a, b):
    """Return an expression representing `a` rotated to the left `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateLeft(a, 10)
    RotateLeft(a, 10)
    >>> simplify(RotateLeft(a, 0))
    a
    >>> simplify(RotateLeft(a, 16))
    a
    """
    s = a.ctx.solver
    _check_rotate_args(a, b)
    return BitVecRef(s.mkTerm(s.mkOp(Kind.BITVECTOR_ROTATE_LEFT, b), a.ast), a.ctx)


def RotateRight(a, b):
    """Return an expression representing `a` rotated to the right `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateRight(a, 10)
    RotateRight(a, 10)
    >>> simplify(RotateRight(a, 0))
    a
    >>> simplify(RotateRight(a, 16))
    a
    """
    s = a.ctx.solver
    _check_rotate_args(a, b)
    return BitVecRef(s.mkTerm(s.mkOp(Kind.BITVECTOR_ROTATE_RIGHT, b), a.ast), a.ctx)


def SignExt(n, a):
    """Return a bit-vector expression with `n` extra sign-bits.

    >>> x = BitVec('x', 16)
    >>> n = SignExt(8, x)
    >>> n.size()
    24
    >>> n
    SignExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(SignExt(6, v0))
    >>> v
    254
    >>> v.size()
    8
    >>> print("%.x" % v.as_long())
    fe
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be an SMT bit-vector expression")
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(Kind.BITVECTOR_SIGN_EXTEND, n), a.ast), a.ctx)


def ZeroExt(n, a):
    """Return a bit-vector expression with `n` extra zero-bits.

    >>> x = BitVec('x', 16)
    >>> n = ZeroExt(8, x)
    >>> n.size()
    24
    >>> n
    ZeroExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(ZeroExt(6, v0))
    >>> v
    2
    >>> v.size()
    8
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be an SMT bit-vector expression")
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(Kind.BITVECTOR_ZERO_EXTEND, n), a.ast), a.ctx)


def RepeatBitVec(n, a):
    """Return an expression representing `n` copies of `a`.

    >>> x = BitVec('x', 8)
    >>> n = RepeatBitVec(4, x)
    >>> n
    RepeatBitVec(4, x)
    >>> n.size()
    32
    >>> v0 = BitVecVal(10, 4)
    >>> print("%.x" % v0.as_long())
    a
    >>> v = simplify(RepeatBitVec(4, v0))
    >>> v.size()
    16
    >>> print("%.x" % v.as_long())
    aaaa
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be an SMT bit-vector expression")
    return BitVecRef(
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(Kind.BITVECTOR_REPEAT, n), a.ast), a.ctx
    )


def BVRedAnd(a):
    """Return the reduction-and expression of `a`.

    >>> x = BitVec('x', 4)
    >>> solve([BVRedAnd(x), BVRedOr(~x)])
    no solution
    """
    if debugging():
        _assert(is_bv(a), "First argument must be an SMT bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_REDAND, a.ast), a.ctx)


def BVRedOr(a):
    """Return the reduction-or expression of `a`.

    >>> x = BitVec('x', 4)
    >>> solve([BVRedAnd(x), BVRedOr(~x)])
    no solution
    """
    if debugging():
        _assert(is_bv(a), "First argument must be an SMT bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(Kind.BITVECTOR_REDOR, a.ast), a.ctx)


def BVAdd(*args):
    """ Create a sum of bit-vectors.

    See also the __add__ overload (+ operator) for BitVecRef.

    >>> x, y, z = BitVecs('x y z', 32)
    >>> BVAdd(x, y, z)
    x + y + z
    """
    return _nary_kind_builder(Kind.BITVECTOR_ADD, *args)


def BVMult(*args):
    """ Create a product of bit-vectors.

    See also the __mul__ overload (* operator) for BitVecRef.

    >>> x, y, z = BitVecs('x y z', 32)
    >>> BVMult(x, y, z)
    x*y*z
    """
    return _nary_kind_builder(Kind.BITVECTOR_MULT, *args)


def BVSub(a, b):
    """ Create a difference of bit-vectors.

    See also the __sub__ overload (- operator) for BitVecRef.

    >>> x, y = BitVecs('x y', 32)
    >>> BVSub(x, y)
    x - y
    """
    return a - b


def BVOr(*args):
    """ Create a bit-wise disjunction of bit-vectors.

    See also the __or__ overload (| operator) for BitVecRef.

    >>> x, y, z = BitVecs('x y z', 32)
    >>> BVOr(x, y, z)
    x | y | z
    """
    return _nary_kind_builder(Kind.BITVECTOR_OR, *args)


def BVAnd(*args):
    """ Create a bit-wise conjunction of bit-vectors.

    See also the __and__ overload (& operator) for BitVecRef.

    >>> x, y, z = BitVecs('x y z', 32)
    >>> BVAnd(x, y, z)
    x & y & z
    """
    return _nary_kind_builder(Kind.BITVECTOR_AND, *args)


def BVXor(*args):
    """ Create a bit-wise exclusive disjunction of bit-vectors.

    See also the __xor__ overload (^ operator) for BitVecRef.

    >>> x, y, z = BitVecs('x y z', 32)
    >>> BVXor(x, y, z)
    x ^ y ^ z
    """
    return _nary_kind_builder(Kind.BITVECTOR_XOR, *args)


def BVNeg(a):
    """ Create a negation (two's complement) of a bit-vector

    See also the __neg__ overload (unary - operator) for BitVecRef.

    >>> x = BitVec('x', 32)
    >>> BVNeg(x)
    -x
    """
    return -a


def BVNot(a):
    """ Create a bitwise not of a bit-vector

    See also the __invert__ overload (unary ~ operator) for BitVecRef.

    >>> x = BitVec('x', 32)
    >>> BVNot(x)
    ~x
    """
    return ~a


#########################################
#
# Arrays
#
#########################################


class ArraySortRef(SortRef):
    """Array sorts."""

    def domain(self):
        """Return the domain of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.domain()
        Int
        """
        return _to_sort_ref(self.ast.getArrayIndexSort(), self.ctx)

    def range(self):
        """Return the range of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.range()
        Bool
        """
        return _to_sort_ref(self.ast.getArrayElementSort(), self.ctx)


class ArrayRef(ExprRef):
    """Array expressions."""

    def sort(self):
        """Return the array sort of the array expression `self`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.sort()
        Array(Int, Bool)
        """
        return _sort(self.ctx, self.ast)

    def domain(self):
        """Shorthand for `self.sort().domain()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.domain()
        Int
        """
        # safe b/c will always yield an ArraySortRef
        return self.sort().domain()  # type: ignore

    def range(self):
        """Shorthand for `self.sort().range()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.range()
        Bool
        """
        # safe b/c will always yield an ArraySortRef
        return self.sort().range()  # type: ignore

    def __getitem__(self, arg):
        """Return the SMT expression `self[arg]`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> i = Int('i')
        >>> a[i]
        a[i]
        >>> a[i].sexpr()
        '(select a i)'
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(
            self.ctx.solver.mkTerm(Kind.SELECT, self.ast, arg.ast), self.ctx
        )

    def arg(self, idx):
        """Get the "argument" (base element) of this constant array.

        >>> b = ConstArray(IntSort(), 1)
        >>> b.arg(0)
        1
        """
        if debugging():
            _assert(is_app(self), "SMT application expected")
            _assert(idx < 1, "Invalid argument index")
        return self.default()

    def default(self):
        """Get the constant element of this (constant) array
        >>> b = ConstArray(IntSort(), 1)
        >>> b.default()
        1
        """
        if debugging():
            _assert(is_app(self), "SMT application expected")
            _assert(is_K(self), "SMT constant array expected")
        return _to_expr_ref(self.ast.getConstArrayBase(), self.ctx)


def is_array_sort(a):
    """ Is this an array sort?

    >>> is_array_sort(ArraySort(BoolSort(), BoolSort()))
    True
    >>> is_array_sort(BoolSort())
    False
    """
    instance_check(a, SortRef)
    return a.ast.isArray()


def is_array(a):
    """Return `True` if `a` is an SMT array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_array(a)
    True
    >>> is_array(Store(a, 0, 1))
    True
    >>> is_array(a[0])
    False
    """
    return isinstance(a, ArrayRef)


def is_const_array(a):
    """Return `True` if `a` is an SMT constant array.

    >>> a = ConstArray(IntSort(), 10)
    >>> is_const_array(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_const_array(a)
    False
    """
    return is_app_of(a, Kind.CONST_ARRAY)


def is_K(a):
    """Return `True` if `a` is an SMT constant array.
    An alias for is_const_array.

    >>> a = ConstArray(IntSort(), 10)
    >>> is_K(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_K(a)
    False
    """
    return is_const_array(a)


def ArraySort(*sig):
    """Return the SMT array sort with the given domain and range sorts.

    >>> A = ArraySort(IntSort(), BoolSort())
    >>> A
    Array(Int, Bool)
    >>> A.domain()
    Int
    >>> A.range()
    Bool
    >>> AA = ArraySort(IntSort(), A)
    >>> AA
    Array(Int, Array(Int, Bool))
    >>> try:
    ...  ArraySort(IntSort(), IntSort(), BoolSort())
    ... except SMTException as e:
    ...  print("failed: %s" % e)
    failed: Unimplemented: multi-domain array
    """
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 1, "At least two arguments expected")
    arity = len(sig) - 1
    r = sig[arity]
    d = sig[0]
    if debugging():
        for s in sig:
            _assert(is_sort(s), "SMT sort expected")
            _assert(s.ctx == r.ctx, "Context mismatch")
    ctx = d.ctx
    if len(sig) == 2:
        return ArraySortRef(ctx.solver.mkArraySort(d.ast, r.ast), ctx)
    else:
        unimplemented("multi-domain array")


def Array(name, dom, rng):
    """Return an array constant named `name` with the given domain and range sorts.

    >>> a = Array('a', IntSort(), IntSort())
    >>> a.sort()
    Array(Int, Int)
    >>> a[0]
    a[0]
    """
    ctx = dom.ctx
    s = ctx.solver.mkArraySort(dom.ast, rng.ast)
    e = ctx.get_var(name, _to_sort_ref(s, ctx))
    return ArrayRef(e, ctx)


def Update(a, i, v):
    """Return an SMT ``store`` array expression. An alias for Store.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Update(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """
    return Store(a, i, v)


def Store(a, i, v):
    """Return an SMT ``store`` array expression.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Store(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """

    if debugging():
        _assert(is_array(a), "First argument must be an SMT array expression")
    i = a.sort().domain().cast(i)
    v = a.sort().range().cast(v)
    ctx = a.ctx
    return _to_expr_ref(ctx.solver.mkTerm(Kind.STORE, a.ast, i.ast, v.ast), ctx)


def Select(a, i):
    """Return an SMT select array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> i = Int('i')
    >>> Select(a, i)
    a[i]
    >>> eq(Select(a, i), a[i])
    True
    """
    if debugging():
        _assert(is_array(a), "First argument must be an SMT array expression")
    return a[i]


def K(dom, v):
    """Return an SMT constant array expression. An alias for ConstArray.

    >>> a = K(IntSort(), 10)
    >>> a
    ConstArray(Int, 10)
    >>> a.sort()
    Array(Int, Int)
    >>> i = Int('i')
    >>> a[i]
    ConstArray(Int, 10)[i]
    >>> simplify(a[i])
    10
    """
    return ConstArray(dom, v)


def ConstArray(dom, v):
    """Return an SMT constant array expression.

    >>> a = ConstArray(IntSort(), 10)
    >>> a
    ConstArray(Int, 10)
    >>> a.sort()
    Array(Int, Int)
    >>> i = Int('i')
    >>> a[i]
    ConstArray(Int, 10)[i]
    >>> simplify(a[i])
    10
    """
    if debugging():
        _assert(is_sort(dom), "SMT sort expected")
    ctx = dom.ctx
    if not is_expr(v):
        v = _py2expr(v, ctx)
    sort = ArraySort(dom, v.sort())
    return ArrayRef(ctx.solver.mkConstArray(sort.ast, v.ast), ctx)


def is_select(a):
    """Return `True` if `a` is an SMT array select application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_select(a)
    False
    >>> i = Int('i')
    >>> is_select(a[i])
    True
    """
    return is_app_of(a, Kind.SELECT)


def is_store(a):
    """Return `True` if `a` is an SMT array ``store`` application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_store(a)
    False
    >>> is_store(Store(a, 0, 1))
    True
    """
    return is_app_of(a, Kind.STORE)


def is_update(a):
    """Return `True` if `a` is an SMT array ``store`` application.
    An alias for is_store.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_update(a)
    False
    >>> is_update(Update(a, 0, 1))
    True
    """
    return is_store(a)


#########################################
#
# Sets
#
#########################################


class SetSortRef(SortRef):
    """Array sorts."""

    def domain(self):
        """Return the domain of the set sort `self`.

        >>> A = SetSort(IntSort())
        >>> A.domain()
        Int
        """
        return _to_sort_ref(self.ast.getSetElementSort(), self.ctx)

    def range(self):
        """Return the "range" of the set sort `self`.
        Included for compatibility with arrays.

        >>> A = SetSort(IntSort())
        >>> A.range()
        Bool
        """
        return BoolSort(self.ctx)


class SetRef(ExprRef):
    """Array expressions."""

    def sort(self):
        """Return the set sort of the set expression `self`.

        >>> a = Set('a', IntSort())
        >>> a.sort()
        Set(Int)
        """
        return _sort(self.ctx, self.ast)

    def domain(self):
        """Shorthand for `self.sort().domain()`.

        >>> a = Set('a', IntSort())
        >>> a.domain()
        Int
        """
        # safe b/c will always yield a SetSortRef
        return self.sort().domain()  # type: ignore

    def range(self):
        """Shorthand for `self.sort().range()`.
        Included for compatibility with arrays.

        >>> a = Set('a', IntSort())
        >>> a.range()
        Bool
        """
        # safe b/c will always yield a SetSortRef
        return self.sort().range()  # type: ignore

    def __getitem__(self, arg):
        """Return the SMT expression `self[arg]`.
        Included for compatibility with arrays.

        >>> a = Set('a', IntSort())
        >>> i = Int('i')
        >>> a[i]
        IsMember(i, a)
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(
            self.ctx.solver.mkTerm(Kind.SET_MEMBER, arg.ast, self.ast), self.ctx
        )

    def default(self):
        """
        Always returns false.

        Included for compatibility with Arrays.

        >>> Set('a', IntSort()).default()
        False

        """
        return BoolRef(self.ctx.solver.mkFalse(), self.ctx)

    def __and__(self, other):
        """ Intersection

        >>> a = Const('a', SetSort(IntSort()))
        >>> b = Const('b', SetSort(IntSort()))
        >>> a & b
        SetIntersect(a, b)
        """
        a, b = _coerce_exprs(self, other)
        return SetIntersect(a, b)

    def __or__(self, other):
        """ Union

        >>> a = Const('a', SetSort(IntSort()))
        >>> b = Const('b', SetSort(IntSort()))
        >>> a | b
        SetUnion(a, b)
        """
        a, b = _coerce_exprs(self, other)
        return SetUnion(a, b)


def SetSort(s):
    """Create a set sort over element sort s"""
    ctx = s.ctx
    instance_check(s, SortRef)
    sort = ctx.solver.mkSetSort(s.ast)
    return SetSortRef(sort, ctx)


def Set(name, elem_sort):
    """Creates a symbolic set of elements"""
    sort = SetSort(elem_sort)
    ctx = _get_ctx(sort.ctx)
    e = ctx.get_var(name, sort)
    return SetRef(e, ctx)


def EmptySet(s):
    """Create the empty set

    >>> EmptySet(IntSort())
    Empty(Set(Int))
    """
    ctx = s.ctx
    sort = SetSort(s)
    return SetRef(ctx.solver.mkEmptySet(sort.ast), ctx)


def FullSet(s):
    """Create the full set

    >>> FullSet(IntSort())
    Full(Set(Int))
    """
    ctx = s.ctx
    sort = SetSort(s)
    return SetRef(ctx.solver.mkUniverseSet(sort.ast), ctx)


def SetUnion(*args):
    """Take the union of sets

    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetUnion(a, b)
    SetUnion(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(Kind.SET_UNION, *[a.ast for a in args]), ctx)


def SetIntersect(*args):
    """Take the intersection of sets

    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetIntersect(a, b)
    SetIntersect(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(Kind.SET_INTER, *[a.ast for a in args]), ctx)


def SetAdd(s, e):
    """Add element e to set s

    >>> a = Const('a', SetSort(IntSort()))
    >>> SetAdd(a, 1)
    SetAdd(a, 1)
    >>> SetAdd(a, 1).arg(0)
    a
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    e = _py2expr(e, ctx)
    return SetRef(ctx.solver.mkTerm(Kind.SET_INSERT, e.ast, s.ast), ctx, True)


def SetDel(s, e):
    """Remove element e to set s

    >>> a = Const('a', SetSort(IntSort()))
    >>> SetDel(a, 1)
    SetDifference(a, Singleton(1))
    """
    return SetDifference(s, Singleton(e))


def SetComplement(s):
    """The complement of set s

    >>> a = Const('a', SetSort(IntSort()))
    >>> SetComplement(a)
    SetComplement(a)
    """
    ctx = s.ctx
    return ArrayRef(ctx.solver.mkTerm(Kind.SET_COMPLEMENT, s.ast), ctx)


def Singleton(s):
    """The single element set of just e

    >>> Singleton(IntVal(1))
    Singleton(1)
    """
    s = _py2expr(s)
    ctx = s.ctx
    return SetRef(ctx.solver.mkTerm(Kind.SET_SINGLETON, s.ast), ctx)


def SetDifference(a, b):
    """The set difference of a and b

    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetDifference(a, b)
    SetDifference(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return SetRef(ctx.solver.mkTerm(Kind.SET_MINUS, a.ast, b.ast), ctx)


def SetMinus(a, b):
    """The set difference of a and b

    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetMinus(a, b)
    SetDifference(a, b)
    """
    return SetDifference(a, b)


def IsMember(e, s):
    """Check if e is a member of set s

    >>> a = Const('a', SetSort(IntSort()))
    >>> IsMember(1, a)
    IsMember(1, a)
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    arg = s.domain().cast(e)
    return BoolRef(ctx.solver.mkTerm(Kind.SET_MEMBER, arg.ast, s.ast), ctx)


def IsSubset(a, b):
    """Check if a is a subset of b

    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> IsSubset(a, b)
    IsSubset(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return BoolRef(ctx.solver.mkTerm(Kind.SET_SUBSET, a.ast, b.ast), ctx)


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
    >>> s.check() != CheckSatResultLiteral("sat")
    False
    """

    def __init__(self, string):
        self.string = string

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
        self.resetAssertions()

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

    def resetAssertions(self):
        """Remove all asserted constraints and backtracking points created
        using `push()`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.resetAssertions()
        >>> s
        []
        """
        self.solver.resetAssertions()
        self.scopes = 0
        self.assertions_ = [[]]

    def reset(self):
        """Fully reset the solver. This actually destroys the solver object in
        the context and recreates this. **This invalidates all objects created
        within this context and using them will most likely crash.**
        
        >>> s = Solver()
        >>> x = Int('x')
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> s.reset()
        >>> s.setOption(incremental=True)
        """
        self.ctx.reset()
        self.solver = self.ctx.solver
        self.resetAssertions()

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
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s += x > 0
        >>> s += x < 2
        >>> s
        [x > 0, x < 2]
        """
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
        >>> s.resetAssertions()
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

    def set(self, *args, **kwargs):
        """Set an option on the solver. Wraps ``setOption()``.

        >>> main_ctx().reset()
        >>> s = Solver()
        >>> s.set(incremental=True)
        >>> s.set('incremental', 'true')
        """
        self.setOption(*args, **kwargs)

    def setOption(self, name=None, value=None, **kwargs):
        """Set options on the solver. Options can either be set via the ``name``
        and ``value`` arguments in the form ``setOption('foo', 'bar')``, or as
        keyword arguments using the syntax ``setOption(foo='bar')``.
        The option value is passed as a string internally. Boolean values are
        properly converted manually, all other types are convertes using
        ``str()``.

        >>> main_ctx().reset()
        >>> s = Solver()
        >>> s.setOption('incremental', True)
        >>> s.setOption(incremental='true')
        """
        if name is not None:
            kwargs[name] = value
        for k, v in kwargs.items():
            _assert(isinstance(k, str), "non-string key " + str(k))
            if isinstance(v, bool):
                v = "true" if v else "false"
            elif not isinstance(v, str):
                v = str(v)
            self.solver.setOption(k, v)

    def getOption(self, name):
        """Get the current value of an option from the solver. The value is
        returned as a string. For type-safe querying use ``getOptionInfo()``.

        >>> main_ctx().reset()
        >>> s = Solver()
        >>> s.setOption(incremental=True)
        >>> s.getOption("incremental")
        'true'
        """
        return self.solver.getOption(name)
    
    def getOptionNames(self):
        """Get all option names that can be used with ``getOption()``,
        ``setOption()`` and ``getOptionInfo()``.

        >>> s = Solver()
        >>> s.getOptionNames()[:3]
        ['abstract-values', 'ackermann', 'approx-branch-depth']
        """
        return self.solver.getOptionNames()

    def getOptionInfo(self, name):
        """Get the current value of an option from the solver. The value is
        returned as a string. For type-safe querying use ``getOptionInfo()``.

        >>> main_ctx().reset()
        >>> s = Solver()
        >>> s.setOption(incremental=False)
        >>> s.getOptionInfo("incremental")
        {'name': 'incremental', 'aliases': [], 'setByUser': True, 'type': <class 'bool'>, 'current': False, 'default': True}
        >>> main_ctx().reset()
        """
        return self.solver.getOptionInfo(name)

    def statistics(self):
        """Return the statistics of this solver.

        >>> c = Context()
        >>> s = Solver(ctx=c)
        >>> a = Int('a', c)
        >>> s.add(a == 0)
        >>> s.check()
        sat
        >>> stats = s.statistics()
        >>> stats['cvc5::CONSTANT']
        {'defaulted': False, 'internal': False, 'value': {'integer type': 1}}
        >>> len(stats.get()) < 10
        True
        >>> len(stats.get(True, True)) > 30
        True
        """
        return self.solver.getStatistics()


def SolverFor(logic, ctx=None, logFile=None):
    """Create a solver customized for the given logic.

    The parameter `logic` is a string. It should be the name of an SMT-LIB
    logic.
    See https://smtlib.cs.uiowa.edu/ for the name of all available logics.
    """

# Pending multiple solvers
# >>> s = SolverFor("QF_LIA")
# >>> x = Int('x')
# >>> s.add(x > 0)
# >>> s.add(x < 2)
# >>> s.check()
# sat
# >>> s.model()
# [x = 1]
# """
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


def Sum(*args):
    """Create the sum of the SMT expressions.

    >>> a, b, c = Ints('a b c')
    >>> Sum(a, b, c)
    a + b + c
    >>> Sum([a, b, c])
    a + b + c
    >>> A = IntVector('a', 5)
    >>> Sum(A)
    a__0 + a__1 + a__2 + a__3 + a__4
    >>> Sum()
    0
    """
    args = _get_args(args)
    if len(args) == 0:
        return 0
    ctx = _ctx_from_ast_arg_list(args)
    if ctx is not None:
        args = _coerce_expr_list(args, ctx)
    return ft.reduce(lambda a, b: a + b, args)


def Product(*args):
    """Create the product of the SMT expressions.

    >>> a, b, c = Ints('a b c')
    >>> Product(a, b, c)
    a*b*c
    >>> Product([a, b, c])
    a*b*c
    >>> A = IntVector('a', 5)
    >>> Product(A)
    a__0*a__1*a__2*a__3*a__4
    >>> Product()
    1
    """
    args = _get_args(args)
    if len(args) == 0:
        return 1
    ctx = _ctx_from_ast_arg_list(args)
    if ctx is not None:
        args = _coerce_expr_list(args, ctx)
    return ft.reduce(lambda a, b: a * b, args)


def substitute(t, *m):
    """Apply substitution m on t, m is a list of pairs of the form (from, to).
    Every occurrence in t of from is replaced with to.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> f = Function('f', IntSort(), IntSort())
    >>> substitute(f(x) + f(y), (f(x), IntVal(1)), (f(y), IntVal(1)))
    1 + 1
    """
    split = _get_args(m)
    if all(isinstance(p, tuple) for p in split):
        m = split
    assert is_expr(t)
    _assert(is_expr(t), "SMT expression expected")
    froms = []
    tos = []
    for subst in m:
        if debugging():
            _assert(isinstance(subst, tuple), "each subst must be a tuple")
            _assert(len(subst) == 2, "each subst must be a pair")
            _assert(
                is_expr(subst[0]) and is_expr(subst[1]),
                "each subst must be from an expression, to an expression",
            )
            _assert(
                subst[0].sort().eq(subst[1].sort()),
                "each subst must be sort-preserving",
            )
        froms.append(subst[0].ast)
        tos.append(subst[1].ast)
    return _to_expr_ref(t.ast.substitute(froms, tos), t.ctx)


def solve(*args, **kwargs):
    """Solve the constraints `*args`.

    This is a simple function for creating demonstrations. It creates a solver,
    configure it using the options in `kwargs`, adds the constraints
    in `args`, and invokes check.

    >>> a = Int('a')
    >>> solve(a > 0, a < 2)
    [a = 1]
    >>> solve(a > 0, a < 2, show=True)
    Problem:
    [a > 0, a < 2]
    Solution:
    [a = 1]
    """
    s = Solver()
    solve_using(s, *args, **kwargs)


def solve_using(s, *args, **kwargs):
    """Solve the constraints `*args` using solver `s`.

    This is a simple function for creating demonstrations.
    It is similar to `solve`, but it uses the given solver `s`.
    It configures solver `s` using the options in `kwargs`,
    adds the constraints in `args`, and invokes check.

    >>> a = Int('a')
    >>> s = Solver()
    >>> solve_using(s, a > 0, a < 2)
    [a = 1]
    >>> solve_using(s, a != 1, show=True)
    Problem:
    [a > 0, a < 2, a != 1]
    no solution
    """
    if debugging():
        _assert(isinstance(s, Solver), "Solver object expected")
    show = False
    if "show" in kwargs:
        if kwargs["show"]:
            show = True
        del kwargs["show"]
    s.set(**kwargs)
    s.add(*args)
    if show:
        print("Problem:")
        print(s)
    r = s.check()
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except SMTException:
            return
    else:
        if show:
            print("Solution:")
        print(s.model())


def prove(claim, **keywords):
    """Try to prove the given claim.

    This is a simple function for creating demonstrations.  It tries to prove
    `claim` by showing the negation is unsatisfiable.

    >>> p, q = Bools('p q')
    >>> prove(Not(And(p, q)) == Or(Not(p), Not(q)))
    proved
    >>> prove(p == True)
    counterexample
    [p = False]
    >>> prove(p == True, show=True)
    [Not(p == True)]
    counterexample
    [p = False]
    """
    if debugging():
        _assert(is_bool(claim), "SMT Boolean expression expected")
    s = Solver()
    s.add(Not(claim))
    if keywords.get("show", False):
        print(s)
    r = s.check()
    if r == unsat:
        print("proved")
    elif r == unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())


def is_sat(*args):
    """Return whether these constraints are satifiable.

    Prints nothing.

    >>> a = Int('a')
    >>> is_sat(a > 0, a < 2)
    True
    """
    s = Solver()
    s.add(args)
    r = s.check()
    _assert(r != unknown, "Unknown result in is_sat")
    return r == sat


def is_tautology(taut):
    """Return whether these constraints hold *for all assignments*.

    Prints nothing.

    >>> p, q = Bools('p q')
    >>> is_tautology(Not(And(p, q)) == Or(Not(p), Not(q)))
    True
    """
    s = Solver()
    s.add(Not(taut))
    r = s.check()
    _assert(r != unknown, "Unknown result in is_tautology")
    return r == unsat


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
            if a.ast.getKind() == Kind.CONSTANT:
                vars_.add(a)
            else:
                for c in a.children():
                    if c not in visit:
                        visit[c] = True
                        q.append(c)
                if a.kind() == Kind.APPLY_UF:
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


#########################################
#
# Floating-Point Arithmetic
#
#########################################


def _coerce_fp_expr_list(alist, ctx):
    first_fp_sort = None
    for a in alist:
        if is_fp(a):
            if first_fp_sort is None:
                first_fp_sort = a.sort()
            elif first_fp_sort == a.sort():
                pass  # OK, same as before
            else:
                # we saw at least 2 different float sorts; something will
                # throw a sort mismatch later, for now assume None.
                first_fp_sort = None
                break

    r = []
    for i in range(len(alist)):
        a = alist[i]
        is_repr = isinstance(a, str) and "2**(" in a and a.endswith(")")
        if is_repr or _is_int(a) or isinstance(a, (float, bool)):
            r.append(FPVal(a, None, first_fp_sort, ctx))
        else:
            r.append(a)
    return _coerce_expr_list(r, ctx)


# FP Sorts

class FPSortRef(SortRef):
    """Floating-point sort."""

    def ebits(self):
        """Retrieves the number of bits reserved for the exponent in the FloatingPoint sort `self`.
        >>> b = FPSort(8, 24)
        >>> b.ebits()
        8
        """
        return self.ast.getFloatingPointExponentSize()

    def sbits(self):
        """Retrieves the number of bits reserved for the significand in the FloatingPoint sort `self`.
        >>> b = FPSort(8, 24)
        >>> b.sbits()
        24
        """
        return self.ast.getFloatingPointSignificandSize()

    def cast(self, val):
        """Try to cast `val` as a floating-point expression.
        >>> b = FPSort(8, 24)
        >>> b.cast(1.0)
        1
        >>> b.cast(1.0).sexpr()
        '(fp #b0 #b01111111 #b00000000000000000000000)'
        """
        if is_expr(val):
            if debugging():
                _assert(self.ctx == val.ctx, "Context mismatch")
            return val
        else:
            return FPVal(val, None, self, self.ctx)


def Float16(ctx=None):
    """Floating-point 16-bit (half) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(ctx.solver.mkFloatingPointSort(5, 11), ctx)


def FloatHalf(ctx=None):
    """Floating-point 16-bit (half) sort."""
    return Float16(ctx)


def Float32(ctx=None):
    """Floating-point 32-bit (single) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(ctx.solver.mkFloatingPointSort(8, 24), ctx)


def FloatSingle(ctx=None):
    """Floating-point 32-bit (single) sort."""
    return Float32(ctx)


def Float64(ctx=None):
    """Floating-point 64-bit (double) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(ctx.solver.mkFloatingPointSort(11, 53), ctx)


def FloatDouble(ctx=None):
    """Floating-point 64-bit (double) sort."""
    return Float64(ctx)


def Float128(ctx=None):
    """Floating-point 128-bit (quadruple) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(ctx.solver.mkFloatingPointSort(15, 113), ctx)


def FloatQuadruple(ctx=None):
    """Floating-point 128-bit (quadruple) sort."""
    return Float128(ctx)


class FPRMSortRef(SortRef):
    """"Floating-point rounding mode sort."""


def is_fp_sort(s):
    """Return True if `s` is a SMT floating-point sort.

    >>> is_fp_sort(FPSort(8, 24))
    True
    >>> is_fp_sort(IntSort())
    False
    """
    return isinstance(s, FPSortRef)


def is_fprm_sort(s):
    """Return True if `s` is a SMT floating-point rounding mode sort.

    >>> is_fprm_sort(FPSort(8, 24))
    False
    >>> is_fprm_sort(RNE().sort())
    True
    """
    return isinstance(s, FPRMSortRef)

# FP Expressions


class FPRef(ExprRef):
    """Floating-point expressions."""

    def sort(self):
        """Return the sort of the floating-point expression `self`.

        >>> x = FP('1.0', FPSort(8, 24))
        >>> x.sort()
        FPSort(8, 24)
        >>> x.sort() == FPSort(8, 24)
        True
        """
        return FPSortRef(self.ast.getSort(), self.ctx)

    def ebits(self):
        """Retrieves the number of bits reserved for the exponent in the FloatingPoint expression `self`.
        >>> b = FPSort(8, 24)
        >>> b.ebits()
        8
        """
        return self.sort().ebits()

    def sbits(self):
        """Retrieves the number of bits reserved for the exponent in the FloatingPoint expression `self`.
        >>> b = FPSort(8, 24)
        >>> b.sbits()
        24
        """
        return self.sort().sbits()

    def as_string(self):
        """Return a SMT floating point expression as a Python string."""
        return str(self.ast)

    def __le__(self, other):
        return fpLEQ(self, other, self.ctx)

    def __lt__(self, other):
        return fpLT(self, other, self.ctx)

    def __ge__(self, other):
        return fpGEQ(self, other, self.ctx)

    def __gt__(self, other):
        return fpGT(self, other, self.ctx)

    def __add__(self, other):
        """Create the SMT expression `self + other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x + y
        x + y
        >>> (x + y).sort()
        FPSort(8, 24)
        """
        return fpAdd(_dflt_rm(), self, other, self.ctx)

    def __radd__(self, other):
        """Create the SMT expression `other + self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> 10 + x
        1.25*(2**3) + x
        """
        return fpAdd(_dflt_rm(), other, self, self.ctx)

    def __sub__(self, other):
        """Create the SMT expression `self - other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x - y
        x - y
        >>> (x - y).sort()
        FPSort(8, 24)
        """
        return fpSub(_dflt_rm(), self, other, self.ctx)

    def __rsub__(self, other):
        """Create the SMT expression `other - self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> 10 - x
        1.25*(2**3) - x
        """
        return fpSub(_dflt_rm(), other, self, self.ctx)

    def __mul__(self, other):
        """Create the SMT expression `self * other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x * y
        x * y
        >>> (x * y).sort()
        FPSort(8, 24)
        >>> 10 * y
        1.25*(2**3) * y
        """
        return fpMul(_dflt_rm(), self, other, self.ctx)

    def __rmul__(self, other):
        """Create the SMT expression `other * self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x * y
        x * y
        >>> x * 10
        x * 1.25*(2**3)
        """
        return fpMul(_dflt_rm(), other, self, self.ctx)

    def __pos__(self):
        """Create the SMT expression `+self`."""
        return self

    def __neg__(self):
        """Create the SMT expression `-self`.

        >>> x = FP('x', Float32())
        >>> -x
        -x
        """
        return fpNeg(self)

    def __div__(self, other):
        """Create the SMT expression `self / other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x / y
        x / y
        >>> (x / y).sort()
        FPSort(8, 24)
        >>> 10 / y
        1.25*(2**3) / y
        """
        return fpDiv(_dflt_rm(), self, other, self.ctx)

    def __rdiv__(self, other):
        """Create the SMT expression `other / self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x / y
        x / y
        >>> x / 10
        x / 1.25*(2**3)
        """
        return fpDiv(_dflt_rm(), other, self, self.ctx)

    def __truediv__(self, other):
        """Create the SMT expression division `self / other`."""
        return self.__div__(other)

    def __rtruediv__(self, other):
        """Create the SMT expression division `other / self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the SMT expression mod `self % other`."""
        return fpRem(self, other)

    def __rmod__(self, other):
        """Create the SMT expression mod `other % self`."""
        return fpRem(other, self)


class FPRMRef(ExprRef):
    """Floating-point rounding mode expressions"""

    def as_string(self):
        """Return a SMT floating point expression as a Python string."""
        return str(self.ast)


def RoundNearestTiesToEven(ctx=None):
    """Round to nearest, with ties broken towards even.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RoundNearestTiesToEven(), x, y)
    fpMul(RNE(), x, y)
    """
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundingMode.ROUND_NEAREST_TIES_TO_EVEN), ctx)


def RNE(ctx=None):
    """Round to nearest, with ties broken towards even.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RNE(), x, y)
    fpMul(RNE(), x, y)
    """
    return RoundNearestTiesToEven(ctx)


def RoundNearestTiesToAway(ctx=None):
    """Round to nearest, with ties broken away from zero.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RoundNearestTiesToAway(), x, y)
    fpMul(RNA(), x, y)
    """
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundingMode.ROUND_NEAREST_TIES_TO_AWAY), ctx)


def RNA(ctx=None):
    """Round to nearest, with ties broken away from zero.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RNA(), x, y)
    fpMul(RNA(), x, y)
    """
    return RoundNearestTiesToAway(ctx)


def RoundTowardPositive(ctx=None):
    """Round towards more positive values.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RoundTowardPositive(), x, y)
    fpMul(RTP(), x, y)
    """
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundingMode.ROUND_TOWARD_POSITIVE), ctx)


def RTP(ctx=None):
    """Round towards more positive values.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RTP(), x, y)
    fpMul(RTP(), x, y)
    """
    return RoundTowardPositive(ctx)


def RoundTowardNegative(ctx=None):
    """Round towards more negative values.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RoundTowardNegative(), x, y)
    fpMul(RTN(), x, y)
    """
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundingMode.ROUND_TOWARD_NEGATIVE), ctx)


def RTN(ctx=None):
    """Round towards more negative values.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RTN(), x, y)
    fpMul(RTN(), x, y)
    """
    return RoundTowardNegative(ctx)


def RoundTowardZero(ctx=None):
    """Round towards zero.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RoundTowardZero(), x, y)
    x * y
    """
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundingMode.ROUND_TOWARD_ZERO), ctx)


def RTZ(ctx=None):
    """Round towards zero.

    See `Section 4.2 of the IEEE standard <https://doi.org/10.1109/IEEESTD.2019.8766229>`
    or `wikipedia <https://en.wikipedia.org/wiki/Floating-point_arithmetic#Rounding_modes>`
    for details on rounding modes.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpMul(RTZ(), x, y)
    x * y
    """
    return RoundTowardZero(ctx)


def is_fprm(a):
    """Return `True` if `a` is a SMT floating-point rounding mode expression.

    >>> rm = RNE()
    >>> is_fprm(rm)
    True
    >>> rm = 1.0
    >>> is_fprm(rm)
    False
    """
    return isinstance(a, FPRMRef)


def is_fprm_value(a):
    """Return `True` if `a` is a SMT floating-point rounding mode numeral value."""
    return is_fprm(a) and _is_numeral(a.ctx, a.ast)


# Global default rounding mode
_dflt_rounding_mode = pc.RoundingMode.ROUND_TOWARD_ZERO
_dflt_fpsort_ebits = 11
_dflt_fpsort_sbits = 53


def get_default_rounding_mode(ctx=None):
    """Retrieves the global default rounding mode."""
    if debugging():
        _assert(isinstance(_dflt_rounding_mode, pc.RoundingMode), "illegal rounding mode")
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(_dflt_rounding_mode), ctx)


def set_default_rounding_mode(rm, ctx=None):
    """Set the default rounding mode

    >>> x, y = FPs('x y', Float32())
    >>> set_default_rounding_mode(RTN())
    >>> sum1 = x + y
    >>> set_default_rounding_mode(RTP())
    >>> sum2 = x + y
    >>> print((sum1 == sum2).sexpr())
    (= (fp.add roundTowardNegative x y) (fp.add roundTowardPositive x y))
    >>> s = SolverFor("QF_FP")
    >>> s += sum1 != sum2
    >>> s.check()
    sat
    >>> m = s.model()
    >>> assert str(m[sum1]) != str(m[sum2])

    Note the the FP term builders can take an explicit rounding mode.
    """
    global _dflt_rounding_mode
    _assert(is_fprm_value(rm), "illegal rounding mode")
    _dflt_rounding_mode = rm.ast.getRoundingModeValue()


def get_default_fp_sort(ctx=None):
    return FPSort(_dflt_fpsort_ebits, _dflt_fpsort_sbits, ctx)


def set_default_fp_sort(ebits, sbits, ctx=None):
    global _dflt_fpsort_ebits
    global _dflt_fpsort_sbits
    _dflt_fpsort_ebits = ebits
    _dflt_fpsort_sbits = sbits


def _dflt_rm(ctx=None):
    return get_default_rounding_mode(ctx)


def _dflt_fps(ctx=None):
    return get_default_fp_sort(ctx)

# FP Numerals


def _fp_ieee_val_sign_py_bool(term):
    sbits, ebits, bv = term.getFloatingPointValue()
    bit = bv.getBitVectorValue()[0]
    if bit == '0':
        return False
    if bit == '1':
        return True
    _assert(False, "Bad sign bit: " + str(bit))


def _fp_ieee_val_significand_bv_py_str(term):
    ebits, sbits, bv = term.getFloatingPointValue()
    return '1.' + bv.getBitVectorValue()[1+ebits:]


def _fp_ieee_val_exponent_bv_py_str(term):
    ebits, sbits, bv = term.getFloatingPointValue()
    return bv.getBitVectorValue()[1:1+ebits]


def _fp_ieee_val_significand_py_uint(term):
    return int(_fp_ieee_val_significand_bv_py_str(term)[2:], 2)


def _fp_ieee_val_significand_py_float(term):
    ebits, sbits, bv = term.getFloatingPointValue()
    uint = _fp_ieee_val_significand_py_uint(term)
    return 1.0 + float(uint) / 2.0 ** (sbits - 1)


def _fp_ieee_val_exponent_py_int(term):
    ebits, sbits, bv = term.getFloatingPointValue()
    return int(_fp_ieee_val_exponent_bv_py_str(term), 2) - 2 ** (ebits - 1) + 1


class FPNumRef(FPRef):
    def sign(self):
        """The sign of the numeral.

        >>> x = FPVal(+1.0, FPSort(8, 24))
        >>> x.sign()
        False
        >>> x = FPVal(-1.0, FPSort(8, 24))
        >>> x.sign()
        True
        """
        return _fp_ieee_val_sign_py_bool(self.ast)

    def significand(self):
        """The significand of the numeral, as a double

        >>> x = FPVal(2.5, FPSort(8, 24))
        >>> x.significand()
        1.25
        """
        return _fp_ieee_val_significand_py_float(self.ast)

    def significand_as_long(self):
        """The significand of the numeral as a long.

        This is missing the 1


        >>> x = FPVal(2.5, FPSort(8, 24))
        >>> x.significand_as_long()
        2097152
        """
        return _fp_ieee_val_significand_py_uint(self.ast)

    def exponent(self, biased=True):
        """The exponent of the numeral.

        >>> x = FPVal(2.5, FPSort(8, 24))
        >>> x.exponent()
        1
        """
        return self.exponent_as_long()

    def exponent_as_long(self):
        """The exponent of the numeral as a long.

        >>> x = FPVal(2.5, FPSort(8, 24))
        >>> x.exponent_as_long()
        1
        """
        return _fp_ieee_val_exponent_py_int(self.ast)

    def isNaN(self):
        """Indicates whether the numeral is a NaN."""
        return self.ast.isFloatingPointNaN()

    def isInf(self):
        """Indicates whether the numeral is +oo or -oo."""
        return self.ast.isFloatingPointNegInf() or self.ast.isFloatingPointPosInf()

    def isZero(self):
        """Indicates whether the numeral is +zero or -zero."""
        return self.ast.isFloatingPointNegZero() or self.ast.isFloatingPointPosZero()

    def isNormal(self):
        """Indicates whether the numeral is normal."""
        unimplemented("FP numeral: isNormal")

    def isSubnormal(self):
        """Indicates whether the numeral is subnormal."""
        unimplemented("FP numeral: isSubnormal")

    def isPositive(self):
        """Indicates whether the numeral is positive."""
        return not self.sign()

    def isNegative(self):
        """Indicates whether the numeral is negative."""
        return self.sign()

    def as_string(self):
        """
        The string representation of the numeral.

        >>> x = FPVal(20, FPSort(8, 24))
        >>> print(x.as_string())
        1.25*(2**4)
        """
        return str(self)
        #return ("FPVal(%s, %s)" % (s, self.sort()))


def is_fp(a):
    """Return `True` if `a` is a SMT floating-point expression.

    >>> b = FP('b', FPSort(8, 24))
    >>> is_fp(b)
    True
    >>> is_fp(b + 1.0)
    True
    >>> is_fp(Int('x'))
    False
    """
    return isinstance(a, FPRef)


def is_fp_value(a):
    """Return `True` if `a` is a SMT floating-point numeral value.

    >>> b = FP('b', FPSort(8, 24))
    >>> is_fp_value(b)
    False
    >>> b = FPVal(1.0, FPSort(8, 24))
    >>> b
    1
    >>> is_fp_value(b)
    True
    """
    return is_fp(a) and _is_numeral(a.ctx, a.ast)


def FPSort(ebits, sbits, ctx=None):
    """Return a SMT floating-point sort of the given sizes. If `ctx=None`, then the global context is used.

    >>> Single = FPSort(8, 24)
    >>> Double = FPSort(11, 53)
    >>> Single
    FPSort(8, 24)
    >>> x = Const('x', Single)
    >>> eq(x, FP('x', FPSort(8, 24)))
    True
    """
    ctx = _get_ctx(ctx)
    return FPSortRef(ctx.solver.mkFloatingPointSort(ebits, sbits), ctx)


def _to_float_str(val, exp=0):
    if isinstance(val, float):
        if math.isnan(val):
            res = "NaN"
        elif val == 0.0:
            sone = math.copysign(1.0, val)
            if sone < 0.0:
                return "-0.0"
            else:
                return "+0.0"
        elif val == float("+inf"):
            res = "+oo"
        elif val == float("-inf"):
            res = "-oo"
        else:
            v = val.as_integer_ratio()
            num = v[0]
            den = v[1]
            rvs = str(num) + "/" + str(den)
            res = rvs + "p" + _to_int_str(exp)
    elif isinstance(val, bool):
        if val:
            res = "1.0"
        else:
            res = "0.0"
    elif _is_int(val):
        res = str(val)
    elif isinstance(val, str):
        inx = val.find("*(2**")
        if inx == -1:
            res = val
        elif val[-1] == ")":
            res = val[0:inx]
            exp = str(int(val[inx + 5:-1]) + int(exp))
        else:
            _assert(False, "String does not have floating-point numeral form.")
    elif debugging():
        _assert(False, "Python value cannot be used to create floating-point numerals.")
    if exp == 0:
        return res
    else:
        return res + "p" + exp


def fpNaN(s):
    """Create a SMT floating-point NaN term.

    >>> s = FPSort(8, 24)
    >>> set_fpa_pretty(True)
    >>> fpNaN(s)
    NaN
    >>> pb = get_fpa_pretty()
    >>> set_fpa_pretty(False)
    >>> fpNaN(s)
    fpNaN(FPSort(8, 24))
    >>> set_fpa_pretty(pb)
    """
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkFloatingPointNaN(s.ebits(), s.sbits()), s.ctx)


def fpPlusInfinity(s):
    """Create a SMT floating-point +oo term.

    >>> s = FPSort(8, 24)
    >>> pb = get_fpa_pretty()
    >>> set_fpa_pretty(True)
    >>> fpPlusInfinity(s)
    +oo
    >>> set_fpa_pretty(False)
    >>> fpPlusInfinity(s)
    fpPlusInfinity(FPSort(8, 24))
    >>> set_fpa_pretty(pb)
    """
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkFloatingPointPosInf(s.ebits(), s.sbits()), s.ctx)


def fpMinusInfinity(s):
    """Create a SMT floating-point -oo term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkFloatingPointNegInf(s.ebits(), s.sbits()), s.ctx)


def fpInfinity(s, negative):
    """Create a SMT floating-point +oo or -oo term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    _assert(isinstance(negative, bool), "expected Boolean flag")
    return fpMinusInfinity(s) if negative else fpPlusInfinity(s)


def fpPlusZero(s):
    """Create a SMT floating-point +0.0 term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkFloatingPointPosZero(s.ebits(), s.sbits()), s.ctx)


def fpMinusZero(s):
    """Create a SMT floating-point -0.0 term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkFloatingPointNegZero(s.ebits(), s.sbits()), s.ctx)


def fpZero(s, negative):
    """Create a SMT floating-point +0.0 or -0.0 term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    _assert(isinstance(negative, bool), "expected Boolean flag")
    return fpMinusZero(s) if negative else fpPlusZero(s)


def FPVal(val, exp=None, fps=None, ctx=None):
    """Return a floating-point value of value `val` and sort `fps`.
    If `ctx=None`, then the global context is used.

    >>> v = FPVal(20.0, FPSort(8, 24))
    >>> v
    1.25*(2**4)
    >>> print("0x%.8x" % v.exponent_as_long())
    0x00000004
    >>> v = FPVal(2.25, FPSort(8, 24))
    >>> v
    1.125*(2**1)
    >>> v = FPVal(-2.25, FPSort(8, 24))
    >>> v
    -1.125*(2**1)
    >>> FPVal(-0.0, FPSort(8, 24))
    -0.0
    >>> FPVal(0.0, FPSort(8, 24))
    +0.0
    >>> FPVal(+0.0, FPSort(8, 24))
    +0.0
    """
    ctx = _get_ctx(ctx)
    if is_fp_sort(exp):
        fps = exp
        exp = None
    elif fps is None:
        fps = _dflt_fps(ctx)
    _assert(is_fp_sort(fps), "sort mismatch")
    if exp is None:
        exp = 0
    if math.isnan(val):
        return fpNaN(fps)
    elif str(val) == "-0.0":
        return fpMinusZero(fps)
    elif val == 0.0 or val == +0.0:
        return fpPlusZero(fps)
    elif val == float("+inf"):
        return fpPlusInfinity(fps)
    elif val == float("-inf"):
        return fpMinusInfinity(fps)
    else:
        # In (sign, exp, significand) order
        bv_str = bin(ctypes.c_uint64.from_buffer(ctypes.c_double(val)).value)[2:]
        bv_str = "0" * (64 - len(bv_str)) + bv_str
        dub = Float64(ctx)
        bv = ctx.solver.mkBitVector(len(bv_str), bv_str, 2)
        fp64 = ctx.solver.mkFloatingPoint(dub.ebits(), dub.sbits(), bv)
        fp_to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_FP, fps.ebits(), fps.sbits())
        fp = ctx.solver.mkTerm(fp_to_fp_op, _dflt_rm(ctx).ast, fp64)
        presimp = FPNumRef(fp, ctx)
        post = simplify(presimp)
        return post


def FP(name, fpsort, ctx=None):
    """Return a floating-point constant named `name`.
    `fpsort` is the floating-point sort.
    If `ctx=None`, then the global context is used.

    >>> x  = FP('x', FPSort(8, 24))
    >>> is_fp(x)
    True
    >>> x.ebits()
    8
    >>> x.sort()
    FPSort(8, 24)
    >>> word = FPSort(8, 24)
    >>> x2 = FP('x', word)
    >>> eq(x, x2)
    True
    """
    if isinstance(fpsort, FPSortRef) and ctx is None:
        ctx = fpsort.ctx
    else:
        ctx = _get_ctx(ctx)
    if debugging():
        _assert(isinstance(fpsort, SortRef), "SMT sort expected")
    ctx = fpsort.ctx
    e = ctx.get_var(name, fpsort)
    return FPRef(e, ctx)


def FPs(names, fpsort, ctx=None):
    """Return an array of floating-point constants.

    >>> x, y, z = FPs('x y z', FPSort(8, 24))
    >>> x.sort()
    FPSort(8, 24)
    >>> x.sbits()
    24
    >>> x.ebits()
    8
    >>> fpMul(RNE(), fpAdd(RNE(), x, y), z)
    fpMul(RNE(), fpAdd(RNE(), x, y), z)
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [FP(name, fpsort, ctx) for name in names]


def fpAbs(a, ctx=None):
    """Create a SMT floating-point absolute value expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FPVal(1.0, s)
    >>> fpAbs(x)
    fpAbs(1)
    >>> y = FPVal(-20.0, s)
    >>> y
    -1.25*(2**4)
    >>> fpAbs(y)
    fpAbs(-1.25*(2**4))
    >>> fpAbs(-1.25*(2**4))
    fpAbs(-1.25*(2**4))
    >>> fpAbs(x).sort()
    FPSort(8, 24)
    """
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    return FPRef(ctx.solver.mkTerm(Kind.FLOATINGPOINT_ABS, a.ast), ctx)


def fpNeg(a, ctx=None):
    """Create a SMT floating-point addition expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> fpNeg(x)
    -x
    >>> fpNeg(x).sort()
    FPSort(8, 24)
    """
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    return FPRef(ctx.solver.mkTerm(Kind.FLOATINGPOINT_NEG, a.ast), ctx)


def _mk_fp_unary(kind, rm, a, ctx):
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_fp(a), "Second argument must be a SMT floating-point expression")
    return FPRef(ctx.solver.mkTerm(kind, rm.as_ast(), a.as_ast()), ctx)


def _mk_fp_unary_pred(kind, a, ctx):
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    if debugging():
        _assert(is_fp(a), "First argument must be a SMT floating-point expression")
    return BoolRef(ctx.solver.mkTerm(kind,  a.as_ast()), ctx)


def _mk_fp_bin(kind, rm, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_fp(a) or is_fp(b), "Second or third argument must be a SMT floating-point expression")
    return FPRef(ctx.solver.mkTerm(kind, rm.as_ast(), a.as_ast(), b.as_ast()), ctx)


def _mk_fp_bin_norm(kind, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if debugging():
        _assert(is_fp(a) or is_fp(b), "First or second argument must be a SMT floating-point expression")
    return FPRef(ctx.solver.mkTerm(kind, a.as_ast(), b.as_ast()), ctx)


def _mk_fp_bin_pred(kind, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if debugging():
        _assert(is_fp(a) or is_fp(b), "First or second argument must be a SMT floating-point expression")
    return BoolRef(ctx.solver.mkTerm(kind, a.as_ast(), b.as_ast()), ctx)


def _mk_fp_tern(kind, rm, a, b, c, ctx):
    ctx = _get_ctx(ctx)
    [a, b, c] = _coerce_fp_expr_list([a, b, c], ctx)
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_fp(a) or is_fp(b) or is_fp(
            c), "Second, third or fourth argument must be a SMT floating-point expression")
    return FPRef(ctx.solver.mkTerm(kind, rm.as_ast(), a.as_ast(), b.as_ast(), c.as_ast()), ctx)


def fpAdd(rm, a, b, ctx=None):
    """Create a SMT floating-point addition expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpAdd(rm, x, y)
    fpAdd(RNE(), x, y)
    >>> fpAdd(RTZ(), x, y) # default rounding mode is RTZ
    x + y
    >>> fpAdd(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Kind.FLOATINGPOINT_ADD, rm, a, b, ctx)


def fpSub(rm, a, b, ctx=None):
    """Create a SMT floating-point subtraction expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpSub(rm, x, y)
    fpSub(RNE(), x, y)
    >>> fpSub(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Kind.FLOATINGPOINT_SUB, rm, a, b, ctx)


def fpMul(rm, a, b, ctx=None):
    """Create a SMT floating-point multiplication expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMul(rm, x, y)
    fpMul(RNE(), x, y)
    >>> fpMul(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Kind.FLOATINGPOINT_MULT, rm, a, b, ctx)


def fpDiv(rm, a, b, ctx=None):
    """Create a SMT floating-point division expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpDiv(rm, x, y)
    fpDiv(RNE(), x, y)
    >>> fpDiv(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Kind.FLOATINGPOINT_DIV, rm, a, b, ctx)


def fpRem(a, b, ctx=None):
    """Create a SMT floating-point remainder expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpRem(x, y)
    fpRem(x, y)
    >>> fpRem(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Kind.FLOATINGPOINT_REM, a, b, ctx)


def fpMin(a, b, ctx=None):
    """Create a SMT floating-point minimum expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMin(x, y)
    fpMin(x, y)
    >>> fpMin(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Kind.FLOATINGPOINT_MIN, a, b, ctx)


def fpMax(a, b, ctx=None):
    """Create a SMT floating-point maximum expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMax(x, y)
    fpMax(x, y)
    >>> fpMax(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Kind.FLOATINGPOINT_MAX, a, b, ctx)


def fpFMA(rm, a, b, c, ctx=None):
    """Create a SMT floating-point fused multiply-add expression.
    """
    return _mk_fp_tern(Kind.FLOATINGPOINT_FMA, rm, a, b, c, ctx)


def fpSqrt(rm, a, ctx=None):
    """Create a SMT floating-point square root expression.
    """
    return _mk_fp_unary(Kind.FLOATINGPOINT_SQRT, rm, a, ctx)


def fpRoundToIntegral(rm, a, ctx=None):
    """Create a SMT floating-point roundToIntegral expression.
    """
    return _mk_fp_unary(Kind.FLOATINGPOINT_RTI, rm, a, ctx)


def fpIsNaN(a, ctx=None):
    """Create a SMT floating-point isNaN expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpIsNaN(x)
    fpIsNaN(x)
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_NAN, a, ctx)


def fpIsInf(a, ctx=None):
    """Create a SMT floating-point isInfinite expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> fpIsInf(x)
    fpIsInf(x)
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_INF, a, ctx)


def fpIsZero(a, ctx=None):
    """Create a SMT floating-point isZero expression.
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_ZERO, a, ctx)


def fpIsNormal(a, ctx=None):
    """Create a SMT floating-point isNormal expression.
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_NORMAL, a, ctx)


def fpIsSubnormal(a, ctx=None):
    """Create a SMT floating-point isSubnormal expression.
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_SUBNORMAL, a, ctx)


def fpIsNegative(a, ctx=None):
    """Create a SMT floating-point isNegative expression.
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_NEG, a, ctx)


def fpIsPositive(a, ctx=None):
    """Create a SMT floating-point isPositive expression.
    """
    return _mk_fp_unary_pred(Kind.FLOATINGPOINT_IS_POS, a, ctx)


def _check_fp_args(a, b):
    if debugging():
        _assert(is_fp(a) or is_fp(b), "First or second argument must be a SMT floating-point expression")


def fpLT(a, b, ctx=None):
    """Create the SMT floating-point expression `other < self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpLT(x, y)
    x < y
    >>> (x < y).sexpr()
    '(fp.lt x y)'
    """
    return _mk_fp_bin_pred(Kind.FLOATINGPOINT_LT, a, b, ctx)


def fpLEQ(a, b, ctx=None):
    """Create the SMT floating-point expression `other <= self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpLEQ(x, y)
    x <= y
    >>> (x <= y).sexpr()
    '(fp.leq x y)'
    """
    return _mk_fp_bin_pred(Kind.FLOATINGPOINT_LEQ, a, b, ctx)


def fpGT(a, b, ctx=None):
    """Create the SMT floating-point expression `other > self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpGT(x, y)
    x > y
    >>> (x > y).sexpr()
    '(fp.gt x y)'
    """
    return _mk_fp_bin_pred(Kind.FLOATINGPOINT_GT, a, b, ctx)


def fpGEQ(a, b, ctx=None):
    """Create the SMT floating-point expression `other >= self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpGEQ(x, y)
    x >= y
    >>> (x >= y).sexpr()
    '(fp.geq x y)'
    """
    return _mk_fp_bin_pred(Kind.FLOATINGPOINT_GEQ, a, b, ctx)


def fpEQ(a, b, ctx=None):
    """Create the SMT floating-point expression `fpEQ(other, self)`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpEQ(x, y)
    fpEQ(x, y)
    >>> fpEQ(x, y).sexpr()
    '(fp.eq x y)'
    """
    return _mk_fp_bin_pred(Kind.FLOATINGPOINT_EQ, a, b, ctx)


def fpNEQ(a, b, ctx=None):
    """Create the SMT floating-point expression `Not(fpEQ(other, self))`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpNEQ(x, y)
    Not(fpEQ(x, y))
    >>> (x != y).sexpr()
    '(distinct x y)'
    """
    return Not(fpEQ(a, b, ctx))


def fpFP(sgn, exp, sig, ctx=None):
    """Create the SMT floating-point value `fpFP(sgn, sig, exp)` from the three bit-vectors sgn, sig, and exp.

    >>> s = FPSort(8, 24)
    >>> x = fpFP(BitVecVal(1, 1), BitVecVal(2**7-1, 8), BitVecVal(2**22, 23))
    >>> print(x)
    fpToFP(Concat(1, 127, 4194304))
    >>> xv = FPVal(-1.5, s)
    >>> print(xv)
    -1.5
    >>> slvr = Solver()
    >>> slvr.add(fpEQ(x, xv))
    >>> slvr.check()
    sat
    >>> xv = FPVal(+1.5, s)
    >>> print(xv)
    1.5
    >>> slvr = Solver()
    >>> slvr.add(fpEQ(x, xv))
    >>> slvr.check()
    unsat
    """
    _assert(is_bv(sgn) and is_bv(exp) and is_bv(sig), "sort mismatch")
    _assert(sgn.sort().size() == 1, "sort mismatch")
    ctx = _get_ctx(ctx)
    _assert(ctx == sgn.ctx == exp.ctx == sig.ctx, "context mismatch")
    bv = BitVecRef(ctx.solver.mkTerm(Kind.BITVECTOR_CONCAT, sgn.ast, exp.ast, sig.ast), ctx)
    sort = FPSort(exp.size(), sig.size()+1)
    return fpBVToFP(bv, sort)


def fpToFP(a1, a2=None, a3=None, ctx=None):
    """Create a SMT floating-point conversion expression from other term sorts
    to floating-point.

    From a floating-point term with different precision:

    >>> x = FPVal(1.0, Float32())
    >>> x_db = fpToFP(RNE(), x, Float64())
    >>> x_db.sort()
    FPSort(11, 53)

    From a real term:

    >>> x_r = RealVal(1.5)
    >>> simplify(fpToFP(RNE(), x_r, Float32()))
    1.5

    From a signed bit-vector term:

    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> simplify(fpToFP(RNE(), x_signed, Float32()))
    -1.25*(2**2)
    """
    ctx = _get_ctx(ctx)
    if is_bv(a1) and is_fp_sort(a2):
        return fpBVToFP(a1, a2, ctx)
    elif is_fprm(a1) and is_fp(a2) and is_fp_sort(a3):
        return fpFPToFP(a1, a2, a3, ctx)
    elif is_fprm(a1) and is_real(a2) and is_fp_sort(a3):
        return fpRealToFP(a1, a2, a3, ctx)
    elif is_fprm(a1) and is_bv(a2) and is_fp_sort(a3):
        return fpSignedToFP(a1, a2, a3, ctx)
    else:
        raise SMTException("Unsupported combination of arguments for conversion to floating-point term.")


def fpBVToFP(v, sort, ctx=None):
    """Create a SMT floating-point conversion expression that represents the
    conversion from a bit-vector term to a floating-point term.

    >>> x_bv = BitVecVal(0x3F800000, 32)
    >>> x_fp = fpBVToFP(x_bv, Float32())
    >>> x_fp
    fpToFP(1065353216)
    >>> simplify(x_fp)
    1
    """
    _assert(is_bv(v), "First argument must be a SMT bit-vector expression")
    _assert(is_fp_sort(sort), "Second argument must be a SMT floating-point sort.")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV, sort.ebits(), sort.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, v.ast), ctx)


def fpFPToFP(rm, v, sort, ctx=None):
    """Create a SMT floating-point conversion expression that represents the
    conversion from a floating-point term to a floating-point term of different precision.

    >>> x_sgl = FPVal(1.0, Float32())
    >>> x_dbl = fpFPToFP(RNE(), x_sgl, Float64())
    >>> x_dbl
    fpToFP(RNE(), 1)
    >>> simplify(x_dbl)
    1
    >>> x_dbl.sort()
    FPSort(11, 53)
    """
    _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression.")
    _assert(is_fp(v), "Second argument must be a SMT floating-point expression.")
    _assert(is_fp_sort(sort), "Third argument must be a SMT floating-point sort.")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_FP, sort.ebits(), sort.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, rm.ast, v.ast), ctx)


def fpRealToFP(rm, v, sort, ctx=None):
    """Create a SMT floating-point conversion expression that represents the
    conversion from a real term to a floating-point term.

    >>> x_r = RealVal(1.5)
    >>> x_fp = fpRealToFP(RNE(), x_r, Float32())
    >>> x_fp
    fpToFP(RNE(), 3/2)
    >>> simplify(x_fp)
    1.5
    """
    _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression.")
    _assert(is_real(v), "Second argument must be a SMT expression or real sort.")
    _assert(is_fp_sort(sort), "Third argument must be a SMT floating-point sort.")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_REAL, sort.ebits(), sort.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, rm.ast, v.ast), ctx)


def fpSignedToFP(rm, v, sort, ctx=None):
    """Create a SMT floating-point conversion expression that represents the
    conversion from a signed bit-vector term (encoding an integer) to a floating-point term.

    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> x_fp = fpSignedToFP(RNE(), x_signed, Float32())
    >>> x_fp
    fpToFP(RNE(), 4294967291)
    >>> simplify(x_fp)
    -1.25*(2**2)
    """
    _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression.")
    _assert(is_bv(v), "Second argument must be a SMT bit-vector expression")
    _assert(is_fp_sort(sort), "Third argument must be a SMT floating-point sort.")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_SBV, sort.ebits(), sort.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, rm.ast, v.ast), ctx)


def fpUnsignedToFP(rm, v, sort, ctx=None):
    """Create a SMT floating-point conversion expression that represents the
    conversion from an unsigned bit-vector term (encoding an integer) to a floating-point term.

    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> x_fp = fpUnsignedToFP(RNE(), x_signed, Float32())
    >>> x_fp
    fpToFP(RNE(), 4294967291)
    >>> simplify(x_fp)
    1*(2**32)
    """
    _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression.")
    _assert(is_bv(v), "Second argument must be a SMT bit-vector expression")
    _assert(is_fp_sort(sort), "Third argument must be a SMT floating-point sort.")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_UBV, sort.ebits(), sort.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, rm.ast, v.ast), ctx)


def fpToFPUnsigned(rm, x, s, ctx=None):
    """Create a SMT floating-point conversion expression, from unsigned bit-vector to floating-point expression."""
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_bv(x), "Second argument must be a SMT bit-vector expression")
        _assert(is_fp_sort(s), "Third argument must be SMT floating-point sort")
    ctx = _get_ctx(ctx)
    to_fp_op = ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_UBV, s.ebits(), s.sbits())
    return FPRef(ctx.solver.mkTerm(to_fp_op, rm.ast, x.ast), ctx)


def fpToSBV(rm, x, s, ctx=None):
    """Create a SMT floating-point conversion expression, from floating-point expression to signed bit-vector.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToSBV(RTZ(), x, BitVecSort(32))
    >>> print(is_fp(x))
    True
    >>> print(is_bv(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_bv(x))
    False
    """
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_fp(x), "Second argument must be a SMT floating-point expression")
        _assert(is_bv_sort(s), "Third argument must be SMT bit-vector sort")
    ctx = _get_ctx(ctx)
    return BitVecRef(ctx.solver.mkTerm(ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_SBV, s.size()), rm.ast, x.ast), ctx)


def fpToUBV(rm, x, s, ctx=None):
    """Create a SMT floating-point conversion expression, from floating-point expression to unsigned bit-vector.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToUBV(RTZ(), x, BitVecSort(32))
    >>> print(is_fp(x))
    True
    >>> print(is_bv(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_bv(x))
    False
    """
    if debugging():
        _assert(is_fprm(rm), "First argument must be a SMT floating-point rounding mode expression")
        _assert(is_fp(x), "Second argument must be a SMT floating-point expression")
        _assert(is_bv_sort(s), "Third argument must be SMT bit-vector sort")
    ctx = _get_ctx(ctx)
    return BitVecRef(ctx.solver.mkTerm(ctx.solver.mkOp(Kind.FLOATINGPOINT_TO_UBV, s.size()), rm.ast, x.ast), ctx)


def fpToReal(x, ctx=None):
    """Create a SMT floating-point conversion expression, from floating-point expression to real.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToReal(x)
    >>> print(is_fp(x))
    True
    >>> print(is_real(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_real(x))
    False
    """
    if debugging():
        _assert(is_fp(x), "First argument must be a SMT floating-point expression")
    ctx = _get_ctx(ctx)
    return ArithRef(ctx.solver.mkTerm(Kind.FLOATINGPOINT_TO_REAL, x.ast), ctx)


#########################################
#
# Datatypes
#
#########################################

def _valid_accessor(acc):
    """Return `True` if acc is pair of the form (String, Datatype or Sort). """
    if not isinstance(acc, tuple):
        return False
    if len(acc) != 2:
        return False
    return isinstance(acc[0], str) and (isinstance(acc[1], Datatype) or is_sort(acc[1]))


class Datatype:
    """Helper class for declaring datatypes.

    >>> List = Datatype('List')
    >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
    >>> List.declare('nil')
    >>> List = List.create()
    >>> # List is now a declaration
    >>> List.nil
    nil
    >>> List.cons(10, List.nil)
    cons(10, nil)
    >>> List.cons(10, List.nil).sort()
    List
    >>> cons = List.cons
    >>> nil  = List.nil
    >>> car  = List.car
    >>> cdr  = List.cdr
    >>> n = cons(1, cons(0, nil))
    >>> n
    cons(1, cons(0, nil))
    >>> simplify(cdr(n))
    cons(0, nil)
    >>> simplify(car(n))
    1
    """

    def __init__(self, name, ctx=None, isCoDatatype=False):
        self.ctx = _get_ctx(ctx)
        self.name = name
        self.constructors = []
        self.isCoDatatype = isCoDatatype

    def declare_core(self, name, rec_name, *args):
        if debugging():
            _assert(isinstance(name, str), "String expected")
            _assert(isinstance(rec_name, str), "String expected")
            _assert(
                all([_valid_accessor(a) for a in args]),
                "Valid list of accessors expected. An accessor is a pair of the form (String, Datatype|Sort)",
            )
        self.constructors.append((name, rec_name, args))

    def declare(self, name, *args):
        """Declare constructor named `name` with the given accessors `args`.
        Each accessor is a pair `(name, sort)`, where `name` is a string and `sort` an SMT sort
        or a reference to the datatypes being declared.
        In the following example `List.declare('cons', ('car', IntSort()), ('cdr', List))`
        declares the constructor named `cons` that builds a new List using an integer and a List.
        It also declares the accessors `car` and `cdr`. The accessor `car` extracts the integer
        of a `cons` cell, and `cdr` the list of a `cons` cell. After all constructors were declared,
        we use the method create() to create the actual datatype in SMT.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        """
        if debugging():
            _assert(isinstance(name, str), "String expected")
            _assert(name != "", "Constructor name cannot be empty")
        return self.declare_core(name, "is-" + name, *args)

    def __repr__(self):
        return "Datatype(%s, %s)" % (self.name, self.constructors)

    def create(self):
        """Create an SMT datatype based on the constructors declared using the method `declare()`.
        The function `CreateDatatypes()` must be used to define mutually recursive datatypes.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.nil
        nil
        >>> List.cons(10, List.nil)
        cons(10, nil)
        >>> Stream = Datatype('Stream', isCoDatatype=True)
        >>> Stream.declare('cons', ('car', IntSort()), ('cdr', Stream))
        >>> Stream.declare('nil')
        >>> Stream = Stream.create()
        >>> a = Const('a', Stream)
        >>> b = Const('b', Stream)
        >>> s = Solver()
        >>> s += a == Stream.cons(0, a)
        >>> s.check()
        sat
        >>> s = Solver()
        >>> s += a == Stream.cons(0, a)
        >>> s += b == Stream.cons(0, b)
        >>> s += a != b
        >>> s.check()
        unsat
        """
        return CreateDatatypes([self])[0]


def CreateDatatypes(*ds):
    """Create mutually recursive SMT datatypes using 1 or more Datatype helper objects.
    In the following example we define a Tree-List using two mutually recursive datatypes.

    >>> TreeList = Datatype('TreeList')
    >>> Tree     = Datatype('Tree')
    >>> # Tree has two constructors: leaf and node
    >>> Tree.declare('leaf', ('val', IntSort()))
    >>> # a node contains a list of trees
    >>> Tree.declare('node', ('children', TreeList))
    >>> TreeList.declare('nil')
    >>> TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))
    >>> Tree, TreeList = CreateDatatypes(Tree, TreeList)
    >>> Tree.val(Tree.leaf(10))
    val(leaf(10))
    >>> simplify(Tree.val(Tree.leaf(10)))
    10
    >>> l1 = TreeList.cons(Tree.leaf(10), TreeList.cons(Tree.leaf(20), TreeList.nil))
    >>> n1 = Tree.node(TreeList.cons(Tree.leaf(10), TreeList.cons(Tree.leaf(20), TreeList.nil)))
    >>> n1
    node(cons(leaf(10), cons(leaf(20), nil)))
    >>> n2 = Tree.node(TreeList.cons(n1, TreeList.nil))
    >>> simplify(n2 == n1)
    False
    >>> simplify(TreeList.car(Tree.children(n2)) == n1)
    True
    """
    ds = _get_args(ds)
    if debugging():
        _assert(len(ds) > 0, "At least one Datatype must be specified")
        _assert(all([isinstance(d, Datatype) for d in ds]), "Arguments must be Datatypes")
        _assert(all([d.ctx == ds[0].ctx for d in ds]), "Context mismatch")
        _assert(all([d.constructors != [] for d in ds]), "Non-empty Datatypes expected")
    ctx = ds[0].ctx
    s = ctx.solver
    num = len(ds)
    uninterp_sorts = {}
    for d in ds:
        uninterp_sorts[d.name] = s.mkUnresolvedDatatypeSort(d.name)
    dt_decls = []
    for i in range(num):
        d = ds[i]
        # Convert from True/False to None/not None
        isCoDatatype = None if not d.isCoDatatype else True
        decl = s.mkDatatypeDecl(d.name, isCoDatatype)
        dt_decls.append(decl)
        con_decls = []
        for j, c in enumerate(d.constructors):
            cname = c[0]
            rname = c[1]
            con = s.mkDatatypeConstructorDecl(cname)
            con_decls.append(decl)
            fs = c[2]
            num_fs = len(fs)
            for k in range(num_fs):
                fname = fs[k][0]
                ftype = fs[k][1]
                if isinstance(ftype, Datatype):
                    if debugging():
                        _assert(
                            ftype.name in uninterp_sorts,
                            "Missing datatype: " + ftype.name,
                        )
                    ftype = uninterp_sorts[ftype.name]
                else:
                    if debugging():
                        _assert(is_sort(ftype), "sort expected")
                    ftype = ftype.ast
                con.addSelector(fname, ftype)
            decl.addConstructor(con)
    dt_sorts = s.mkDatatypeSorts(dt_decls)
    # Create a field for every constructor, recognizer and accessor
    result = []
    for i in range(num):
        dref = DatatypeSortRef(dt_sorts[i], ctx)
        num_cs = dref.num_constructors()
        for j in range(num_cs):
            cref = dref.constructor(j)
            cref_name = cref.name()
            cref_arity = cref.arity()
            if cref_arity == 0:
                cref = cref()
            setattr(dref, cref_name, cref)
            rref = dref.recognizer(j)
            setattr(dref, "is_" + cref_name, rref)
            for k in range(cref_arity):
                aref = dref.accessor(j, k)
                setattr(dref, aref.name(), aref)
        result.append(dref)
    return tuple(result)


class DatatypeSortRef(SortRef):
    """Datatype sorts."""

    def __init__(self, ast, ctx=None):
        super().__init__(ast, ctx)
        self.dt = ast.getDatatype()

    def num_constructors(self):
        """Return the number of constructors in the given datatype.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a declaration
        >>> List.num_constructors()
        2
        """
        return self.dt.getNumConstructors()

    def constructor(self, idx):
        """Return a constructor of the datatype `self`.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a declaration
        >>> List.num_constructors()
        2
        >>> List.constructor(0)
        cons
        >>> List.constructor(1)
        nil
        """
        if debugging():
            _assert(idx < self.num_constructors(), "Invalid constructor index")
        return DatatypeConstructorRef(self.dt[idx], self.ctx)

    def recognizer(self, idx):
        """In SMT, each constructor has an associated recognizer predicate.
        If the constructor is named `name`, then the recognizer `is_name`.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a SMT declaration
        >>> List.num_constructors()
        2
        >>> List.recognizer(0)
        is_cons
        >>> List.recognizer(1)
        is_nil
        >>> simplify(List.is_nil(List.cons(10, List.nil)))
        False
        >>> simplify(List.is_cons(List.cons(10, List.nil)))
        True
        >>> l = Const('l', List)
        >>> simplify(List.is_cons(l))
        is_cons(l)
        """
        if debugging():
            _assert(idx < self.num_constructors(), "Invalid recognizer index")
        return DatatypeRecognizerRef(self.dt[idx], self.ctx)

    def accessor(self, i, j):
        """In SMT, each constructor has 0 or more accessor.
        The number of accessors is equal to the arity of the constructor.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0)
        cons
        >>> num_accs = List.constructor(0).arity()
        >>> num_accs
        2
        >>> List.accessor(0, 0)
        car
        >>> List.accessor(0, 1)
        cdr
        >>> List.constructor(1)
        nil
        >>> num_accs = List.constructor(1).arity()
        >>> num_accs
        0
        """
        if debugging():
            _assert(i < self.num_constructors(), "Invalid constructor index")
            _assert(j < self.constructor(i).arity(), "Invalid accessor index")
        return DatatypeSelectorRef(self.dt[i][j], self.ctx)


class DatatypeConstructorRef(FuncDeclRef):
    def __init__(self, datatype, ctx=None, r=False):
        super().__init__(datatype.getTerm(), ctx, r)
        self.dt = datatype

    def arity(self):
        """Return the number of arguments of a constructor.

        The number of accessors is equal to the arity of the constructor.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0).arity()
        2
        """
        return self.dt.getNumSelectors()

    def domain(self, i):
        """Return the sort of the argument `i` of a constructor.
        This method assumes that `0 <= i < self.arity()`.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0).domain(0)
        Int
        """
        return _to_sort_ref(self.ast.getSort().getDatatypeConstructorDomainSorts()[i], self.ctx)

    def range(self):
        """Return the sort of the range of a function declaration.
        For constants, this is the sort of the constant.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0).range()
        List
        """
        return _to_sort_ref(self.ast.getSort().getDatatypeConstructorCodomainSort(), self.ctx)

    def __call__(self, *args):
        """Apply this constructor.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0)(1, List.nil)
        cons(1, nil)

        The arguments must be SMT expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a SMT
        integer, then the argument is automatically converted into a
        SMT integer.
        """
        return _higherorder_apply(self, args, Kind.APPLY_CONSTRUCTOR)


class DatatypeSelectorRef(FuncDeclRef):
    def __init__(self, datatype, ctx=None, r=False):
        super().__init__(datatype.getTerm(), ctx, r)
        self.dt = datatype

    def arity(self):
        """Return the number of arguments of a selector (always 1).
        """
        return 1

    def domain(self, i):
        """Return the sort of the argument `i` of a selector.
        This method assumes that `0 <= i < self.arity()`.
        """
        _assert(i == 0, "Selectors take 1 argument")
        return _to_sort_ref(self.ast.getSort().getDatatypeSelectorDomainSort(), self.ctx)

    def range(self):
        """Return the sort of the range of a function declaration.
        For constants, this is the sort of the constant.
        """
        return _to_sort_ref(self.ast.getSort().getDatatypeSelectorCodomainSort(), self.ctx)

    def __call__(self, *args):
        """Apply this selector.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> l = List.cons(1, List.nil)
        >>> solve([1 != List.car(l)])
        no solution

        The arguments must be SMT expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a SMT
        integer, then the argument is automatically converted into a
        SMT integer.
        """
        return _higherorder_apply(self, args, Kind.APPLY_SELECTOR)


class DatatypeRecognizerRef(FuncDeclRef):
    def __init__(self, constructor, ctx=None, r=False):
        super().__init__(constructor.getTesterTerm(), ctx, r)
        self.constructor = constructor

    def arity(self):
        """Return the number of arguments of a selector (always 1).
        """
        return 1

    def domain(self, i):
        """Return the sort of the argument `i` of a selector.
        This method assumes that `0 <= i < self.arity()`.
        """
        _assert(i == 0, "Recognizers take 1 argument")
        return _to_sort_ref(self.ast.getSort().getDatatypeTesterDomainSort(), self.ctx)

    def range(self):
        """Return the sort of the range of a function declaration.
        For constants, this is the sort of the constant.
        """
        return BoolSort(self.ctx)

    def __call__(self, *args):
        """Apply this tester (a.k.a., recognizer).

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> l = List.cons(1, List.nil)
        >>> solve([List.is_nil(l)])
        no solution

        The arguments must be SMT expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a SMT
        integer, then the argument is automatically converted into a
        SMT integer.
        """
        return _higherorder_apply(self, args, Kind.APPLY_TESTER)



class DatatypeRef(ExprRef):
    """Datatype expressions."""

    def sort(self):
        """Return the datatype sort of the datatype expression `self`."""
        return DatatypeSortRef(self.as_ast().getSort(), self.ctx)


def TupleSort(name, sorts, ctx=None):
    """Create a named tuple sort base on a set of underlying sorts

    Returns the tuple datatype, its constructor, and a list of accessors, in order.

    >>> pair, mk_pair, (first, second) = TupleSort("pair", [IntSort(), BoolSort()])
    >>> b = Bool('b')
    >>> i = Int('i')
    >>> p = mk_pair(i, b)
    >>> p
    pair(i, b)
    >>> solve([b != second(p)])
    no solution
    """
    tuple = Datatype(name, ctx)
    projects = [("project%d" % i, sorts[i]) for i in range(len(sorts))]
    tuple.declare(name, *projects)
    tuple = tuple.create()
    return tuple, tuple.constructor(0), [tuple.accessor(0, i) for i in range(len(sorts))]


def DisjointSum(name, sorts, ctx=None):
    """Create a named tagged union sort base on a set of underlying sorts.

    See `this page <https://en.wikipedia.org/wiki/Tagged_union>` for
    information about tagged unions.

    Returns the created datatype and a tuple of (injector, extractor) pairs for
    the different variants.

    >>> sum, ((inject0, extract0), (inject1, extract1)) = DisjointSum("+", [IntSort(), BoolSort()])
    >>> b = Bool('b')
    >>> i, j = Ints('i j')
    >>> solve([inject0(i) == inject1(b)])
    no solution
    >>> solve([inject0(i) == inject0(j), extract0(inject0(i)) == 5])
    [i = 5, j = 5]
    """
    sum = Datatype(name, ctx)
    for i in range(len(sorts)):
        sum.declare("inject%d" % i, ("project%d" % i, sorts[i]))
    sum = sum.create()
    return sum, [(sum.constructor(i), sum.accessor(i, 0)) for i in range(len(sorts))]


#########################################
#
# Quantifiers
#
#########################################


class QuantifierRef(BoolRef):
    """Universally and Existentially quantified formulas."""

    def as_ast(self):
        return self.ast

    def sort(self):
        """Return the Boolean sort"""
        return BoolSort(self.ctx)

    def is_forall(self):
        """Return `True` if `self` is a universal quantifier.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.is_forall()
        True
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_forall()
        False
        """
        return self.ast.getKind() == Kind.FORALL

    def is_exists(self):
        """Return `True` if `self` is an existential quantifier.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.is_exists()
        False
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_exists()
        True
        """
        return self.ast.getKind() == Kind.EXISTS

    def is_lambda(self):
        """Return `True` if `self` is a lambda expression.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = Lambda(x, f(x))
        >>> q.is_lambda()
        True
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_lambda()
        False
        """
        return self.ast.getKind() == Kind.LAMBDA

    def body(self):
        """Return the expression being quantified.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.body()
        f(x) == 0
        """
        return _to_expr_ref(self.ast[1], self.ctx)

    def num_vars(self):
        """Return the number of variables bounded by this quantifier.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> x = Int('x')
        >>> y = Int('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.num_vars()
        2
        """
        return self.ast[0].getNumChildren()

    def var_name(self, idx):
        """Return a string representing a name used when displaying the quantifier.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> x = Int('x')
        >>> y = Int('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.var_name(0)
        'x'
        >>> q.var_name(1)
        'y'
        """
        if debugging():
            _assert(idx < self.num_vars(), "Invalid variable idx")
        return str(self.ast[0][idx])

    def var_sort(self, idx):
        """Return the sort of a bound variable.

        >>> f = Function('f', IntSort(), RealSort(), IntSort())
        >>> x = Int('x')
        >>> y = Real('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.var_sort(0)
        Int
        >>> q.var_sort(1)
        Real
        """
        if debugging():
            _assert(idx < self.num_vars(), "Invalid variable idx")
        return _to_sort_ref(self.ast[0][idx].getSort(), self.ctx)

    def children(self):
        """Return a list containing a single element self.body()

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.children()
        [f(x) == 0]
        """
        return [self.body()]


def is_quantifier(a):
    """Return `True` if `a` is an SMT quantifier, including lambda expressions.

    >>> f = Function('f', IntSort(), IntSort())
    >>> x = Int('x')
    >>> q = ForAll(x, f(x) == 0)
    >>> p = Lambda(x, f(x) == 0)
    >>> is_quantifier(q)
    True
    >>> is_quantifier(p)
    True
    >>> is_quantifier(f(x))
    False
    """
    return isinstance(a, QuantifierRef)


def _mk_quant(vs, body, kind):
    """Make a quantifier or lambda.
    Replaces constants in `vs` with bound variables.
    """
    if not isinstance(vs, list):
        vs = [vs]
    c = vs[0].ctx
    s = c.solver
    consts = [v.ast for v in vs]
    vars_ = [s.mkVar(v.sort().ast, str(v)) for v in vs]
    subbed_body = body.ast.substitute(consts, vars_)
    ast = s.mkTerm(kind, s.mkTerm(Kind.VARIABLE_LIST, *vars_), subbed_body)
    return QuantifierRef(ast, c)


def ForAll(vs, body):
    """Create a forall formula.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> x = Int('x')
    >>> y = Int('y')
    >>> ForAll([x, y], f(x, y) >= x)
    ForAll([x, y], f(x, y) >= x)
    """
    return _mk_quant(vs, body, Kind.FORALL)


def Exists(vs, body):
    """Create a exists formula.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> x = Int('x')
    >>> y = Int('y')
    >>> q = Exists([x, y], f(x, y) >= x)
    >>> q
    Exists([x, y], f(x, y) >= x)
    """
    return _mk_quant(vs, body, Kind.EXISTS)


def Lambda(vs, body):
    """Create a lambda expression.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> mem0 = Array('mem0', IntSort(), IntSort())
    >>> lo, hi, e, i = Ints('lo hi e i')
    >>> mem1 = Lambda([i], If(And(lo <= i, i <= hi), e, mem0[i]))
    >>> mem1
    Lambda(i, If(And(lo <= i, i <= hi), e, mem0[i]))
    """
    return _mk_quant(vs, body, Kind.LAMBDA)
