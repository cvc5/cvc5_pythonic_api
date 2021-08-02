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


TODO:
    * multiple solvers
    * FP
    * DT
    * quantifiers & variables
"""
from .z3printer import *
from fractions import Fraction
from decimal import Decimal
import ctypes
import decimal
import sys
import math
import io
import functools as ft
import operator as op

import pycvc5 as pc
from pycvc5 import kinds

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
        return BoolRef(c.solver.mkTerm(kinds.Equal, a.as_ast(), b.as_ast()), c)

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
        return BoolRef(c.solver.mkTerm(kinds.Distinct, a.as_ast(), b.as_ast()), c)

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
        if is_app_of(self, kinds.ApplyUf):
            return _to_expr_ref(list(self.ast)[0], self.ctx)  # type: ignore
        else:
            raise SMTException("Declarations for non-function applications")

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
        return str(self)

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
        args = _get_args(args)
        num = len(args)
        if debugging():
            _assert(
                num == self.arity(),
                "Incorrect number of arguments to %s" % self,
            )
        _args = []
        for i in range(num):
            tmp = self.domain(i).cast(args[i])
            _args.append(tmp.as_ast())
        return _to_expr_ref(
            self.ctx.solver.mkTerm(kinds.ApplyUf, self.ast, *_args), self.ctx
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
    if sort.isFloatingPoint():
        if ast.getKind() == kinds.ConstFP:
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
        kinds.ConstBoolean,
        kinds.ConstBV,
        kinds.ConstFP,
        kinds.ConstRational,
        kinds.Emptyset,
        kinds.UniverseSet,
        kinds.Constant,
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
    return k == kinds.Variable


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
    return _to_expr_ref(ctx.solver.mkTerm(kinds.Ite, a.ast, b.ast, c.ast), ctx)


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
    return BoolRef(ctx.solver.mkTerm(kinds.Distinct, [a.ast for a in args]), ctx)


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
    return is_app_of(a, kinds.ConstBoolean) and a.ast == a.ctx.solver.mkTrue()


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
    return is_app_of(a, kinds.ConstBoolean) and a.ast == a.ctx.solver.mkFalse()


def is_and(a):
    """Return `True` if `a` is an SMT and expression.

    >>> p, q = Bools('p q')
    >>> is_and(And(p, q))
    True
    >>> is_and(Or(p, q))
    False
    """
    return is_app_of(a, kinds.And)


def is_or(a):
    """Return `True` if `a` is an SMT or expression.

    >>> p, q = Bools('p q')
    >>> is_or(Or(p, q))
    True
    >>> is_or(And(p, q))
    False
    """
    return is_app_of(a, kinds.Or)


def is_implies(a):
    """Return `True` if `a` is an SMT implication expression.

    >>> p, q = Bools('p q')
    >>> is_implies(Implies(p, q))
    True
    >>> is_implies(And(p, q))
    False
    """
    return is_app_of(a, kinds.Implies)


def is_not(a):
    """Return `True` if `a` is an SMT not expression.

    >>> p = Bool('p')
    >>> is_not(p)
    False
    >>> is_not(Not(p))
    True
    """
    return is_app_of(a, kinds.Not)


def is_eq(a):
    """Return `True` if `a` is an SMT equality expression.

    >>> x, y = Ints('x y')
    >>> is_eq(x == y)
    True
    """
    return is_app_of(a, kinds.Equal)


def is_distinct(a):
    """Return `True` if `a` is an SMT distinct expression.

    >>> x, y, z = Ints('x y z')
    >>> is_distinct(x == y)
    False
    >>> is_distinct(Distinct(x, y, z))
    True
    """
    return is_app_of(a, kinds.Distinct)


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
    return BoolRef(ctx.solver.mkTerm(kinds.Implies, a.as_ast(), b.as_ast()), ctx)


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
    return BoolRef(ctx.solver.mkTerm(kinds.Xor, a.as_ast(), b.as_ast()), ctx)


def Not(a, ctx=None):
    """Create an SMT not expression or probe.

    >>> p = Bool('p')
    >>> Not(Not(p))
    Not(Not(p))
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    return BoolRef(ctx.solver.mkTerm(kinds.Not, a.as_ast()), ctx)


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
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args) - 1]
    if isinstance(last_arg, Context):
        ctx = args[len(args) - 1]
        args = args[: len(args) - 1]
    elif len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        ctx = args[0][0]
        args = [a for a in args[0]]
    else:
        ctx = None
    args = _get_args(args)
    ctx = _get_ctx(_ctx_from_ast_arg_list(args, ctx))
    if debugging():
        _assert(
            ctx is not None,
            "At least one of the arguments must be an SMT expression or probe",
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(kinds.And, [a.ast for a in args]), ctx)


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
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args) - 1]
    if isinstance(last_arg, Context):
        ctx = args[len(args) - 1]
        args = args[: len(args) - 1]
    elif len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        ctx = args[0][0]
        args = [a for a in args[0]]
    else:
        ctx = None
    args = _get_args(args)
    ctx = _get_ctx(_ctx_from_ast_arg_list(args, ctx))
    if debugging():
        _assert(
            ctx is not None,
            "At least one of the arguments must be an SMT expression or probe",
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(kinds.Or, [a.ast for a in args]), ctx)


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
        return ArithRef(a.ctx.solver.mkTerm(kinds.Plus, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the SMT expression `other + self`.

        >>> x = Int('x')
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Plus, b.ast, a.ast), self.ctx)

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
        return ArithRef(a.ctx.solver.mkTerm(kinds.Mult, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the SMT expression `other * self`.

        >>> x = Real('x')
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Mult, b.ast, a.ast), self.ctx)

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
        return ArithRef(a.ctx.solver.mkTerm(kinds.Minus, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the SMT expression `other - self`.

        >>> x = Int('x')
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Minus, b.ast, a.ast), self.ctx)

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
        return ArithRef(a.ctx.solver.mkTerm(kinds.Pow, a.ast, b.ast), self.ctx)

    def __rpow__(self, other):
        """Create the SMT expression `other**self` (** is the power operator).

        >>> x = Real('x')
        >>> 2**x
        2**x
        >>> (2**x).sort()
        Real
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Pow, b.ast, a.ast), self.ctx)

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
            k = kinds.IntsDivision
        else:
            k = kinds.Division
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
            k = kinds.IntsDivision
        else:
            k = kinds.Division
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
        return ArithRef(a.ctx.solver.mkTerm(kinds.IntsModulus, a.ast, b.ast), self.ctx)

    def __rmod__(self, other):
        """Create the SMT expression `other%self`.

        >>> x = Int('x')
        >>> 10 % x
        10%x
        """
        a, b = _coerce_exprs(self, other)
        if debugging():
            _assert(a.sort().is_int(), "SMT integer expression expected")
        return ArithRef(a.ctx.solver.mkTerm(kinds.IntsModulus, b.ast, a.ast), self.ctx)

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = Int('x')
        >>> -x
        -x
        """
        return ArithRef(self.ctx.solver.mkTerm(kinds.Uminus, self.ast), self.ctx)

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
        return BoolRef(a.ctx.solver.mkTerm(kinds.Leq, a.ast, b.ast), self.ctx)

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
        return BoolRef(a.ctx.solver.mkTerm(kinds.Lt, a.ast, b.ast), self.ctx)

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
        return BoolRef(a.ctx.solver.mkTerm(kinds.Gt, a.ast, b.ast), self.ctx)

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
        return BoolRef(a.ctx.solver.mkTerm(kinds.Geq, a.ast, b.ast), self.ctx)


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
    return term.getKind() in [kinds.ConstRational, kinds.ConstBV, kinds.ConstBoolean, kinds.ConstRoundingmode, kinds.ConstFP]


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
    return is_app_of(a, kinds.Plus)


def is_mul(a):
    """Return `True` if `a` is an expression of the form b * c.

    >>> x, y = Ints('x y')
    >>> is_mul(x * y)
    True
    >>> is_mul(x - y)
    False
    """
    return is_app_of(a, kinds.Mult)


def is_sub(a):
    """Return `True` if `a` is an expression of the form b - c.

    >>> x, y = Ints('x y')
    >>> is_sub(x - y)
    True
    >>> is_sub(x + y)
    False
    """
    return is_app_of(a, kinds.Minus)


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
    return is_app_of(a, kinds.Division)


def is_idiv(a):
    """Return `True` if `a` is an expression of the form b div c.

    >>> x, y = Ints('x y')
    >>> is_idiv(x / y)
    True
    >>> is_idiv(x + y)
    False
    """
    return is_app_of(a, kinds.IntsDivision)


def is_mod(a):
    """Return `True` if `a` is an expression of the form b % c.

    >>> x, y = Ints('x y')
    >>> is_mod(x % y)
    True
    >>> is_mod(x + y)
    False
    """
    return is_app_of(a, kinds.IntsModulus)


def is_le(a):
    """Return `True` if `a` is an expression of the form b <= c.

    >>> x, y = Ints('x y')
    >>> is_le(x <= y)
    True
    >>> is_le(x < y)
    False
    """
    return is_app_of(a, kinds.Leq)


def is_lt(a):
    """Return `True` if `a` is an expression of the form b < c.

    >>> x, y = Ints('x y')
    >>> is_lt(x < y)
    True
    >>> is_lt(x == y)
    False
    """
    return is_app_of(a, kinds.Lt)


def is_ge(a):
    """Return `True` if `a` is an expression of the form b >= c.

    >>> x, y = Ints('x y')
    >>> is_ge(x >= y)
    True
    >>> is_ge(x == y)
    False
    """
    return is_app_of(a, kinds.Geq)


def is_gt(a):
    """Return `True` if `a` is an expression of the form b > c.

    >>> x, y = Ints('x y')
    >>> is_gt(x > y)
    True
    >>> is_gt(x == y)
    False
    """
    return is_app_of(a, kinds.Gt)


def is_is_int(a):
    """Return `True` if `a` is an expression of the form IsInt(b).

    >>> x = Real('x')
    >>> is_is_int(IsInt(x))
    True
    >>> is_is_int(x)
    False
    """
    return is_app_of(a, kinds.IsInteger)


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
    return is_app_of(a, kinds.ToReal)


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
    return is_app_of(a, kinds.ToInteger)


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
    return ArithRef(ctx.solver.mkTerm(kinds.ToReal, a.ast), ctx)


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
    return ArithRef(ctx.solver.mkTerm(kinds.ToInteger, a.ast), ctx)


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
    return BoolRef(ctx.solver.mkTerm(kinds.IsInteger, a.ast), ctx)


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
        return self.ast.getBVSize()

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAdd, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the SMT expression `other + self`.

        >>> x = BitVec('x', 32)
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAdd, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVMult, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the SMT expression `other * self`.

        >>> x = BitVec('x', 32)
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVMult, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSub, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the SMT expression `other - self`.

        >>> x = BitVec('x', 32)
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSub, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVOr, a.ast, b.ast), self.ctx)

    def __ror__(self, other):
        """Create the SMT expression bitwise-or `other | self`.

        >>> x = BitVec('x', 32)
        >>> 10 | x
        10 | x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVOr, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAnd, a.ast, b.ast), self.ctx)

    def __rand__(self, other):
        """Create the SMT expression bitwise-or `other & self`.

        >>> x = BitVec('x', 32)
        >>> 10 & x
        10 & x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAnd, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVXor, a.ast, b.ast), self.ctx)

    def __rxor__(self, other):
        """Create the SMT expression bitwise-xor `other ^ self`.

        >>> x = BitVec('x', 32)
        >>> 10 ^ x
        10 ^ x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVXor, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVNeg, self.ast), self.ctx)

    def __invert__(self):
        """Create the SMT expression bitwise-not `~self`.

        >>> x = BitVec('x', 32)
        >>> ~x
        ~x
        >>> solve([~(~x) != x])
        no solution
        """
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVNot, self.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSdiv, a.ast, b.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSdiv, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSmod, a.ast, b.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSmod, b.ast, a.ast), self.ctx)

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
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSle, a.ast, b.ast), self.ctx)

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
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSlt, a.ast, b.ast), self.ctx)

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
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSgt, a.ast, b.ast), self.ctx)

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
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSge, a.ast, b.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAshr, a.ast, b.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVShl, a.ast, b.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAshr, b.ast, a.ast), self.ctx)

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
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVShl, b.ast, a.ast), self.ctx)


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
        return ArithRef(ctx.solver.mkTerm(kinds.BVToNat, a.ast), ctx)


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
    return BitVecRef(ctx.solver.mkTerm(ctx.solver.mkOp(kinds.IntToBV, num_bits), a.ast), ctx)


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

    >>> v = BitVecVal(10, 32)
    >>> v
    10
    >>> print("0x%.8x" % v.as_long())
    0x0000000a
    """
    if is_bv_sort(bv):
        ctx = bv.ctx
        size = bv.size()
    else:
        size = bv
        ctx = _get_ctx(ctx)
    string = "{{:0{}b}}".format(size).format(val)
    return BitVecNumRef(ctx.solver.mkBitVector(string), ctx)


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
    return BitVecRef(ctx.solver.mkTerm(kinds.BVConcat, *[a.ast for a in args]))


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
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(kinds.BVExtract, high, low), a.ast), a.ctx
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
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUle, a.ast, b.ast), a.ctx)


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
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUlt, a.ast, b.ast), a.ctx)


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
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUge, a.ast, b.ast), a.ctx)


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
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUgt, a.ast, b.ast), a.ctx)


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
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVUdiv, a.ast, b.ast), a.ctx)


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
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVUrem, a.ast, b.ast), a.ctx)


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
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVSrem, a.ast, b.ast), a.ctx)


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
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVLshr, a.ast, b.ast), a.ctx)


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
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVRotateLeft, b), a.ast), a.ctx)


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
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVRotateRight, b), a.ast), a.ctx)


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
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVSignExtend, n), a.ast), a.ctx)


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
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVZeroExtend, n), a.ast), a.ctx)


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
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(kinds.BVRepeat, n), a.ast), a.ctx
    )


def BVRedAnd(a):
    """Return the reduction-and expression of `a`.

    >>> x = BitVec('x', 4)
    >>> solve([BVRedAnd(x), BVRedOr(~x)])
    no solution
    """
    if debugging():
        _assert(is_bv(a), "First argument must be an SMT bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVRedand, a.ast), a.ctx)


def BVRedOr(a):
    """Return the reduction-or expression of `a`.

    >>> x = BitVec('x', 4)
    >>> solve([BVRedAnd(x), BVRedOr(~x)])
    no solution
    """
    if debugging():
        _assert(is_bv(a), "First argument must be an SMT bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVRedor, a.ast), a.ctx)

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
            self.ctx.solver.mkTerm(kinds.Select, self.ast, arg.ast), self.ctx
        )

    def arg(self, idx):
        """Get the "argument" (base element) of this constant array.

        >>> b = K(IntSort(), 1)
        >>> b.arg(0)
        1
        """
        if debugging():
            _assert(is_app(self), "SMT application expected")
            _assert(idx < 1, "Invalid argument index")
        return self.default()

    def default(self):
        """Get the constant element of this (constant) array
        >>> b = K(IntSort(), 1)
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

    >>> a = K(IntSort(), 10)
    >>> is_const_array(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_const_array(a)
    False
    """
    return is_app_of(a, kinds.ConstArray)


def is_K(a):
    """Return `True` if `a` is an SMT constant array.

    >>> a = K(IntSort(), 10)
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
    """Return an SMT store array expression.

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
    if debugging():
        _assert(is_array(a), "First argument must be an SMT array expression")
    i = a.sort().domain().cast(i)
    v = a.sort().range().cast(v)
    ctx = a.ctx
    return _to_expr_ref(ctx.solver.mkTerm(kinds.Store, a.ast, i.ast, v.ast), ctx)


def Store(a, i, v):
    """Return an SMT store array expression.

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
    return Update(a, i, v)


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
    """Return an SMT constant array expression.

    >>> a = K(IntSort(), 10)
    >>> a
    K(Int, 10)
    >>> a.sort()
    Array(Int, Int)
    >>> i = Int('i')
    >>> a[i]
    K(Int, 10)[i]
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
    return is_app_of(a, kinds.Select)


def is_store(a):
    """Return `True` if `a` is an SMT array store application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_store(a)
    False
    >>> is_store(Store(a, 0, 1))
    True
    """
    return is_app_of(a, kinds.Store)


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
        member(i, a)
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(
            self.ctx.solver.mkTerm(kinds.Member, arg.ast, self.ast), self.ctx
        )

    def default(self):
        """
        Always returns false.

        Included for compatibility with Arrays.

        >>> Set('a', IntSort()).default()
        False

        """
        return BoolRef(self.ctx.solver.mkFalse(), self.ctx)


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
    union(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(kinds.Union, [a.ast for a in args]), ctx)


def SetIntersect(*args):
    """Take the union of sets
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetIntersect(a, b)
    intersection(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(kinds.Intersection, [a.ast for a in args]), ctx)


def SetAdd(s, e):
    """Add element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetAdd(a, 1)
    insert(a, 1)
    >>> SetAdd(a, 1).arg(0)
    a
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    e = _py2expr(e, ctx)
    return SetRef(ctx.solver.mkTerm(kinds.Insert, e.ast, s.ast), ctx, True)


def SetDel(s, e):
    """Remove element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetDel(a, 1)
    setminus(a, singleton(1))
    """
    return SetDifference(s, Singleton(e))


def SetComplement(s):
    """The complement of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetComplement(a)
    complement(a)
    """
    ctx = s.ctx
    return ArrayRef(ctx.solver.mkTerm(kinds.Complement, s.ast), ctx)


def Singleton(s):
    """The single element set of just e
    >>> Singleton(IntVal(1))
    singleton(1)
    """
    s = _py2expr(s)
    ctx = s.ctx
    return SetRef(ctx.solver.mkTerm(kinds.Singleton, s.ast), ctx)


def SetDifference(a, b):
    """The set difference of a and b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetDifference(a, b)
    setminus(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return SetRef(ctx.solver.mkTerm(kinds.Setminus, a.ast, b.ast), ctx)


def SetMinus(a, b):
    """The set difference of a and b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetMinus(a, b)
    setminus(a, b)
    """
    return SetDifference(a, b)


def IsMember(e, s):
    """Check if e is a member of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> IsMember(1, a)
    member(1, a)
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    arg = s.domain().cast(e)
    return BoolRef(ctx.solver.mkTerm(kinds.Member, arg.ast, s.ast), ctx)


def IsSubset(a, b):
    """Check if a is a subset of b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> IsSubset(a, b)
    subset(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return BoolRef(ctx.solver.mkTerm(kinds.Subset, a.ast, b.ast), ctx)


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

    def set(self, **kwargs):
        for k, v in kwargs:
            _assert(isinstance(k, str), "non-string key " + str(k))
            _assert(isinstance(v, str), "non-string key " + str(v))
            self.solver.setOption(k, v)


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



#########################################
#
# Floating-Point Arithmetic
#
#########################################


# Global default rounding mode
_dflt_rounding_mode = pc.RoundTowardZero
_dflt_fpsort_ebits = 11
_dflt_fpsort_sbits = 53


def get_default_rounding_mode(ctx=None):
    """Retrieves the global default rounding mode."""
    if _dflt_rounding_mode == pc.RoundTowardZero:
        return RTZ(ctx)
    elif _dflt_rounding_mode == pc.RoundTowardNegative:
        return RTN(ctx)
    elif _dflt_rounding_mode == pc.RoundTowardPositive:
        return RTP(ctx)
    elif _dflt_rounding_mode == pc.RoundNearestTiesToEven:
        return RNE(ctx)
    elif _dflt_rounding_mode == pc.RoundNearestTiesToAway:
        return RNA(ctx)


_ROUNDING_MODES = frozenset({
    pc.RoundTowardZero,
    pc.RoundTowardNegative,
    pc.RoundTowardPositive,
    pc.RoundNearestTiesToEven,
    pc.RoundNearestTiesToAway
})


def set_default_rounding_mode(rm, ctx=None):
    global _dflt_rounding_mode
    if is_fprm_value(rm):
        _dflt_rounding_mode = rm.decl().kind()
    else:
        _assert(_dflt_rounding_mode in _ROUNDING_MODES, "illegal rounding mode")
        _dflt_rounding_mode = rm


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
        return self.ast.getFPExponentSize()

    def sbits(self):
        """Retrieves the number of bits reserved for the significand in the FloatingPoint sort `self`.
        >>> b = FPSort(8, 24)
        >>> b.sbits()
        24
        """
        return self.ast.getFPSignificandSize()

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


class FPRMRef(ExprRef):
    """Floating-point rounding mode expressions"""

    def as_string(self):
        """Return a SMT floating point expression as a Python string."""
        return str(self.ast)


def RoundNearestTiesToEven(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundNearestTiesToEven), ctx)


def RNE(ctx=None):
    return RoundNearestTiesToEven(ctx)


def RoundNearestTiesToAway(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundNearestTiesToAway), ctx)


def RNA(ctx=None):
    return RoundNearestTiesToAway(ctx)


def RoundTowardPositive(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundTowardPositive), ctx)


def RTP(ctx=None):
    return RoundTowardPositive(ctx)


def RoundTowardNegative(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundTowardNegative), ctx)


def RTN(ctx=None):
    return RoundTowardNegative(ctx)


def RoundTowardZero(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(ctx.solver.mkRoundingMode(pc.RoundTowardZero), ctx)


def RTZ(ctx=None):
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


def is_fp(a):
    """Return `True` if `a` is a SMT floating-point expression.

    >>> b = FP('b', FPSort(8, 24))
    >>> is_fp(b)
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
    return FPNumRef(s.ctx.solver.mkNaN(s.ebits(), s.sbits()), s.ctx)


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
    return FPNumRef(s.ctx.solver.mkPosInf(s.ebits(), s.sbits()), s.ctx)


def fpMinusInfinity(s):
    """Create a SMT floating-point -oo term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkNegInf(s.ebits(), s.sbits()), s.ctx)


def fpInfinity(s, negative):
    """Create a SMT floating-point +oo or -oo term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    _assert(isinstance(negative, bool), "expected Boolean flag")
    return fpMinusInfinity(s) if negative else fpPlusInfinity(s)


def fpPlusZero(s):
    """Create a SMT floating-point +0.0 term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkPosZero(s.ebits(), s.sbits()), s.ctx)


def fpMinusZero(s):
    """Create a SMT floating-point -0.0 term."""
    _assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(s.ctx.solver.mkNegZero(s.ebits(), s.sbits()), s.ctx)


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
        bv = ctx.solver.mkBitVector(bv_str)
        fp64 = ctx.solver.mkFloatingPoint(dub.ebits(), dub.sbits(), bv)
        fp_to_fp_op = ctx.solver.mkOp(kinds.FPToFpFP, fps.ebits(), fps.sbits())
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
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [FP(name, fpsort, ctx) for name in names]

