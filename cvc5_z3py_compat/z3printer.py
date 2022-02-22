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

from . import z3 as cvc
import cvc5 as pc
from cvc5 import Kind


def _assert(cond, msg):
    cvc._assert(cond, msg)


##############################
#
# Configuration
#
##############################

# Z3 operator names to Z3Py
_z3_op_to_str = {
    Kind.Equal: "==",
    Kind.Distinct: "Distinct",
    Kind.Ite: "If",
    Kind.And: "And",
    Kind.Or: "Or",
    Kind.Xor: "Xor",
    Kind.Not: "Not",
    Kind.Add: "+",
    Kind.Sub: "-",
    Kind.Pow: "**",
    Kind.Neg: "-",
    Kind.Mult: "*",
    Kind.Implies: "Implies",
    Kind.IntsDivision: "/",
    Kind.Division: "/",
    Kind.IntsModulus: "%",
    Kind.ToReal: "ToReal",
    Kind.ToInteger: "ToInt",
    Kind.IsInteger: "IsInt",
    Kind.BVAdd: "+",
    Kind.BVSub: "-",
    Kind.BVMult: "*",
    Kind.BVOr: "|",
    Kind.BVAnd: "&",
    Kind.BVNot: "~",
    Kind.BVXor: "^",
    Kind.BVNeg: "-",
    Kind.BVUdiv: "UDiv",
    Kind.BVSdiv: "/",
    Kind.BVSmod: "%",
    Kind.BVSrem: "SRem",
    Kind.BVUrem: "URem",
    Kind.BVRotateLeft: "RotateLeft",
    Kind.BVRotateRight: "RotateRight",
    Kind.Leq: "<=",
    Kind.Lt: "<",
    Kind.Geq: ">=",
    Kind.Gt: ">",
    Kind.BVSle: "<=",
    Kind.BVSlt: "<",
    Kind.BVSge: ">=",
    Kind.BVSgt: ">",
    Kind.BVUle: "ULE",
    Kind.BVUlt: "ULT",
    Kind.BVUge: "UGE",
    Kind.BVUgt: "UGT",
    Kind.BVSignExtend: "SignExt",
    Kind.BVZeroExtend: "ZeroExt",
    Kind.BVRepeat: "RepeatBitVec",
    Kind.BVAshr: ">>",
    Kind.BVShl: "<<",
    Kind.BVLshr: "LShR",
    Kind.BVConcat: "Concat",
    Kind.BVExtract: "Extract",
    Kind.BVToNat: "BV2Int",
    Kind.Select: "Select",
    Kind.Store: "Store",
    Kind.ConstArray: "ConstArray",
    Kind.SeqConcat: "Concat",
    Kind.SeqPrefix: "PrefixOf",
    Kind.SeqSuffix: "SuffixOf",
    Kind.SeqUnit: "Unit",
    Kind.SeqContains: "Contains",
    Kind.SeqReplace: "Replace",
    Kind.SeqAt: "At",
    Kind.SeqNth: "Nth",
    Kind.SeqIndexof: "IndexOf",
    Kind.SeqLength: "Length",
    Kind.SetSubset: "IsSubset",
    Kind.SetMinus: "SetDifference",
    Kind.SetComplement: "SetComplement",
    Kind.SetSingleton: "Singleton",
    Kind.SetInsert: "SetAdd",
    Kind.SetInter: "SetIntersect",
    Kind.SetUnion: "SetUnion",
    Kind.SetMember: "IsMember",
    Kind.StringToInt: "StrToInt",
    Kind.StringFromInt: "IntToStr",
    # Kind.Seq_in_re: "InRe",
    # Kind.Seq_to_re: "Re",
    Kind.RegexpPlus: "Plus",
    Kind.RegexpStar: "Star",
    Kind.RegexpUnion: "Union",
    Kind.RegexpRange: "Range",
    Kind.RegexpInter: "Intersect",
    Kind.RegexpComplement: "Complement",
    Kind.FPIsNan: "fpIsNaN",
    Kind.FPIsInf: "fpIsInf",
    Kind.FPIsZero: "fpIsZero",
    Kind.FPIsNormal: "fpIsNormal",
    Kind.FPIsSubnormal: "fpIsMinusnormal",
    Kind.FPIsNeg: "fpIsNegative",
    Kind.FPIsPos: "fpIsPositive",
}

# List of infix operators
_z3_infix = [
    Kind.Equal,
    Kind.Add,
    Kind.Pow,
    Kind.Sub,
    Kind.Mult,
    Kind.Division,
    Kind.IntsDivision,
    Kind.IntsModulus,
    Kind.Leq,
    Kind.Lt,
    Kind.Geq,
    Kind.Gt,
    Kind.BVAdd,
    Kind.BVSub,
    Kind.BVMult,
    Kind.BVSdiv,
    Kind.BVSmod,
    Kind.BVOr,
    Kind.BVAnd,
    Kind.BVXor,
    Kind.BVSdiv,
    Kind.BVSle,
    Kind.BVSlt,
    Kind.BVSge,
    Kind.BVSgt,
    Kind.BVAshr,
    Kind.BVShl,
]

_z3_unary = [Kind.Neg, Kind.BVNeg, Kind.BVNot]

# Precedence
_z3_precedence = {
    Kind.Pow: 0,
    Kind.Neg: 1,
    Kind.BVNeg: 1,
    Kind.BVNot: 1,
    Kind.Mult: 2,
    Kind.Division: 2,
    Kind.IntsDivision: 2,
    Kind.IntsModulus: 2,
    Kind.BVMult: 2,
    Kind.BVSdiv: 2,
    Kind.BVSmod: 2,
    Kind.Add: 3,
    Kind.Sub: 3,
    Kind.BVAdd: 3,
    Kind.BVSub: 3,
    Kind.BVAshr: 4,
    Kind.BVShl: 4,
    Kind.BVAnd: 5,
    Kind.BVXor: 6,
    Kind.BVOr: 7,
    Kind.Leq: 8,
    Kind.Lt: 8,
    Kind.Geq: 8,
    Kind.Gt: 8,
    Kind.Equal: 8,
    Kind.BVSle: 8,
    Kind.BVSlt: 8,
    Kind.BVSge: 8,
    Kind.BVSgt: 8,
    Kind.BVUle: 8,
    Kind.BVUlt: 8,
    Kind.BVUge: 8,
    Kind.BVUgt: 8,
}

_z3_fpa_rm_strings = {
    "roundNearestTiesToEven": "RoundNearestTiesToEven()",
    "roundNearestTiesToAway": "RoundNearestTiesToAway()",
    "roundTowardPositive": "RoundTowardPositive()",
    "roundTowardNegative": "RoundTowardNegative()",
    "roundTowardZero": "RoundTowardZero()",
}
_z3_fpa_rm_short_strings = {
    "roundNearestTiesToEven": "RNE()",
    "roundNearestTiesToAway": "RNA()",
    "roundTowardPositive": "RTP()",
    "roundTowardNegative": "RTN()",
    "roundTowardZero": "RTZ()",
}

# FPA operators
_z3_op_to_fpa_normal_str = {
    Kind.FPAdd: "fpAdd",
    Kind.FPSub: "fpSub",
    Kind.FPNeg: "fpNeg",
    Kind.FPMult: "fpMul",
    Kind.FPDiv: "fpDiv",
    Kind.FPRem: "fpRem",
    Kind.FPAbs: "fpAbs",
    Kind.FPMin: "fpMin",
    Kind.FPMax: "fpMax",
    Kind.FPFma: "fpFMA",
    Kind.FPSqrt: "fpSqrt",
    Kind.FPRti: "fpRoundToIntegral",

    Kind.FPEq: "fpEQ",
    Kind.FPLt: "fpLT",
    Kind.FPGt: "fpGT",
    Kind.FPLeq: "fpLEQ",
    Kind.FPGeq: "fpGEQ",

    Kind.FPToFpGeneric: "fpFP",
    Kind.FPToFpFP: "fpToFP",
    Kind.FPToFpUnsignedBV: "fpToFP",
    Kind.FPToFpSignedBV: "fpToFP",
    Kind.FPToFpReal: "fpToFP",
    Kind.FPToFpIeeeBV: "fpToFP",
    Kind.FPToUbv: "fpToUBV",
    Kind.FPToSbv: "fpToSBV",
    Kind.FPToReal: "fpToReal",
}

_z3_op_to_fpa_pretty_str = {
    Kind.FPAdd: "+", Kind.FPSub: "-", Kind.FPMult: "*", Kind.FPDiv: "/",
    Kind.FPRem: "%", Kind.FPNeg: "-",

    Kind.FPEq: "fpEQ", Kind.FPLt: "<", Kind.FPGt: ">", Kind.FPLeq: "<=",
    Kind.FPGeq: ">="
}

_z3_fpa_infix = [
    Kind.FPAdd, Kind.FPSub, Kind.FPMult, Kind.FPDiv, Kind.FPRem,
    Kind.FPLt, Kind.FPGt, Kind.FPLeq, Kind.FPGeq
]

def _is_assoc(k):
    return (
        k == Kind.BVOr
        or k == Kind.BVXor
        or k == Kind.BVAnd
        or k == Kind.Add
        or k == Kind.BVAdd
        or k == Kind.Mult
        or k == Kind.BVMult
    )


def _is_left_assoc(k):
    return _is_assoc(k) or k == Kind.Sub or k == Kind.BVSub


def _is_add(k):
    return k == Kind.Add or k == Kind.BVAdd


def _is_sub(k):
    return k == Kind.Sub or k == Kind.BVSub


if sys.version < "3":
    import codecs

    def u(x):
        return codecs.unicode_escape_decode(x)[0]


else:

    def u(x):
        return x


_z3_infix_compact = [
    Kind.Mult,
    Kind.BVMult,
    Kind.Division,
    Kind.Pow,
    Kind.IntsDivision,
    Kind.IntsModulus,
    Kind.BVSdiv,
    Kind.BVSmod,
]

_ellipses = "..."

##############################
#
# End of Configuration
#
##############################


def _support_pp(a):
    return isinstance(a, (cvc.ExprRef, cvc.SortRef)) or isinstance(a, list) or isinstance(a, tuple)


_infix_map = {}
_unary_map = {}
_infix_compact_map = {}

for _k in _z3_infix:
    _infix_map[_k] = True
for _k in _z3_unary:
    _unary_map[_k] = True

for _k in _z3_infix_compact:
    _infix_compact_map[_k] = True


def _is_infix(k):
    global _infix_map
    return _infix_map.get(k, False)


def _is_infix_compact(k):
    global _infix_compact_map
    return _infix_compact_map.get(k, False)


def _is_unary(k):
    global _unary_map
    return _unary_map.get(k, False)


def _op_name(a):
    k = a.kind()
    n = _z3_op_to_str.get(k, None)
    if n is None:
        if k in [Kind.Constant, Kind.ConstFP, Kind.ConstRoundingmode, Kind.Variable, Kind.UninterpretedSortValue]:
            return str(a.ast)
        if k == Kind.InternalKind:
            # Hack to handle DT selectors and constructors
            return str(a.ast)
        if isinstance(a, cvc.FuncDeclRef):
            f = a
        else:
            raise Exception("Cannot print: " + str(k))
        return f.name()
    else:
        return n


def _get_precedence(k):
    global _z3_precedence
    return _z3_precedence.get(k, 100000)


class FormatObject:
    def is_compose(self):
        return False

    def is_choice(self):
        return False

    def is_indent(self):
        return False

    def is_string(self):
        return False

    def is_linebreak(self):
        return False

    def is_nil(self):
        return True

    def children(self):
        return []

    def as_tuple(self):
        return None

    def space_upto_nl(self):
        return (0, False)

    def flat(self):
        return self


class NAryFormatObject(FormatObject):
    def __init__(self, fs):
        assert all([isinstance(a, FormatObject) for a in fs])
        self.children = fs

    def children(self):
        return self.children


class ComposeFormatObject(NAryFormatObject):
    def is_compose(self):
        return True

    def as_tuple(self):
        return ("compose", [a.as_tuple() for a in self.children])

    def space_upto_nl(self):
        r = 0
        for child in self.children:
            s, nl = child.space_upto_nl()
            r = r + s
            if nl:
                return (r, True)
        return (r, False)

    def flat(self):
        return compose([a.flat() for a in self.children])


class ChoiceFormatObject(NAryFormatObject):
    def is_choice(self):
        return True

    def as_tuple(self):
        return ("choice", [a.as_tuple() for a in self.children])

    def space_upto_nl(self):
        return self.children[0].space_upto_nl()

    def flat(self):
        return self.children[0].flat()


class IndentFormatObject(FormatObject):
    def __init__(self, indent, child):
        assert isinstance(child, FormatObject)
        self.indent = indent
        self.child = child

    def children(self):
        return [self.child]

    def as_tuple(self):
        return ("indent", self.indent, self.child.as_tuple())

    def space_upto_nl(self):
        return self.child.space_upto_nl()

    def flat(self):
        return indent(self.indent, self.child.flat())

    def is_indent(self):
        return True


class LineBreakFormatObject(FormatObject):
    def __init__(self):
        self.space = " "

    def is_linebreak(self):
        return True

    def as_tuple(self):
        return "<line-break>"

    def space_upto_nl(self):
        return (0, True)

    def flat(self):
        return to_format(self.space)


class StringFormatObject(FormatObject):
    def __init__(self, string):
        assert isinstance(string, str)
        self.string = string

    def is_string(self):
        return True

    def as_tuple(self):
        return self.string

    def space_upto_nl(self):
        return (getattr(self, "size", len(self.string)), False)


def fits(f, space_left):
    s, nl = f.space_upto_nl()
    return s <= space_left


def to_format(arg, size=None):
    if isinstance(arg, FormatObject):
        return arg
    else:
        r = StringFormatObject(str(arg))
        if size is not None:
            r.size = size
        return r


def compose(*args):
    if len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        args = args[0]
    return ComposeFormatObject(args)


def indent(i, arg):
    return IndentFormatObject(i, arg)


def group(arg):
    return ChoiceFormatObject([arg.flat(), arg])


def line_break():
    return LineBreakFormatObject()


def _len(a):
    if isinstance(a, StringFormatObject):
        return getattr(a, "size", len(a.string))
    else:
        return len(a)


def seq(args, sep=",", space=True):
    nl = line_break()
    if not space:
        nl.space = ""
    r = []
    num = len(args)
    if num > 0:
        r.append(args[0])
        for i in range(num - 1):
            r.append(to_format(sep))
            r.append(nl)
            r.append(args[i + 1])
    return compose(r)


def seq1(header, args, lp="(", rp=")"):
    return group(
        compose(
            to_format(header),
            to_format(lp),
            indent(len(lp) + _len(header), seq(args)),
            to_format(rp),
        )
    )


def seq2(header, args, i=4, lp="(", rp=")"):
    if len(args) == 0:
        return compose(to_format(header), to_format(lp), to_format(rp))
    else:
        return group(
            compose(
                indent(len(lp), compose(to_format(lp), to_format(header))),
                indent(i, compose(seq(args), to_format(rp))),
            )
        )


def seq3(args, lp="(", rp=")"):
    if len(args) == 0:
        return compose(to_format(lp), to_format(rp))
    else:
        return group(indent(len(lp), compose(to_format(lp), seq(args), to_format(rp))))


class StopPPException(Exception):
    def __str__(self):
        return "pp-interrupted"


class PP:
    def __init__(self):
        self.max_lines = 200
        self.max_width = 60
        self.bounded = False
        self.max_indent = 40

    def pp_string(self, f, indent):
        if not self.bounded or self.pos <= self.max_width:
            sz = _len(f)
            if self.bounded and self.pos + sz > self.max_width:
                self.out.write(u(_ellipses))
            else:
                self.pos = self.pos + sz
                self.ribbon_pos = self.ribbon_pos + sz
                self.out.write(u(f.string))

    def pp_compose(self, f, indent):
        for c in f.children:
            self.pp(c, indent)

    def pp_choice(self, f, indent):
        space_left = self.max_width - self.pos
        if space_left > 0 and fits(f.children[0], space_left):
            self.pp(f.children[0], indent)
        else:
            self.pp(f.children[1], indent)

    def pp_line_break(self, f, indent):
        self.pos = indent
        self.ribbon_pos = 0
        self.line = self.line + 1
        if self.line < self.max_lines:
            self.out.write(u("\n"))
            for i in range(indent):
                self.out.write(u(" "))
        else:
            self.out.write(u("\n..."))
            raise StopPPException()

    def pp(self, f, indent):
        if isinstance(f, str):
            self.pp_string(f, indent)
        elif f.is_string():
            self.pp_string(f, indent)
        elif f.is_indent():
            self.pp(f.child, min(indent + f.indent, self.max_indent))
        elif f.is_compose():
            self.pp_compose(f, indent)
        elif f.is_choice():
            self.pp_choice(f, indent)
        elif f.is_linebreak():
            self.pp_line_break(f, indent)
        else:
            return

    def __call__(self, out, f):
        try:
            self.pos = 0
            self.ribbon_pos = 0
            self.line = 0
            self.out = out
            self.pp(f, 0)
        except StopPPException:
            return


class Formatter:
    def __init__(self):
        global _ellipses
        self.max_depth = 20
        self.max_args = 128
        self.rational_to_decimal = False
        self.precision = 10
        self.ellipses = to_format(_ellipses)
        self.max_visited = 10000
        self.fpa_pretty = True

    def pp_ellipses(self):
        return self.ellipses

    def pp_arrow(self):
        return " ->"

    def pp_unknown(self):
        return "<unknown>"

    def pp_name(self, a):
        return to_format(_op_name(a))

    def is_infix(self, a):
        return _is_infix(a)

    def is_unary(self, a):
        return _is_unary(a)

    def get_precedence(self, a):
        return _get_precedence(a)

    def is_infix_compact(self, a):
        return _is_infix_compact(a)

    def is_infix_unary(self, a):
        return self.is_infix(a) or self.is_unary(a)

    def add_paren(self, a):
        return compose(to_format("("), indent(1, a), to_format(")"))

    def pp_sort(self, s):
        if isinstance(s, cvc.ArraySortRef):
            return seq1("Array", (self.pp_sort(s.domain()), self.pp_sort(s.range())))
        elif isinstance(s, cvc.BitVecSortRef):
            return seq1("BitVec", (to_format(s.size()),))
        elif isinstance(s, cvc.SetSortRef):
            return seq1("Set", (self.pp_sort(s.domain()), ))
        elif isinstance(s, cvc.FPSortRef):
            return seq1("FPSort", (to_format(s.ebits()), to_format(s.sbits())))
        # elif isinstance(s, cvc.ReSortRef):
        #     return seq1("ReSort", (self.pp_sort(s.basis()),))
        # elif isinstance(s, cvc.SeqSortRef):
        #     if s.is_string():
        #         return to_format("String")
        #     return seq1("Seq", (self.pp_sort(s.basis()),))
        else:
            return to_format(s.name())

    def pp_const(self, a):
        k = a.kind()
        if k == Kind.SetEmpty:
            return self.pp_set("Empty", a)
        # elif k == Z3_OP_SEQ_EMPTY:
        #     return self.pp_set("Empty", a)
        elif k == Kind.SetUniverse:
            return self.pp_set("Full", a)
        return self.pp_name(a)

    def pp_int(self, a):
        return to_format(a.as_string())

    def pp_rational(self, a):
        if not self.rational_to_decimal:
            return to_format(a.as_string())
        else:
            return to_format(a.as_decimal(self.precision))

    def pp_bool(self, a):
        s = str(a.ast)
        return to_format(s[0].upper() + s[1:])

    def pp_algebraic(self, a):
        return to_format(a.as_decimal(self.precision))

    def pp_string(self, a):
        return to_format('"' + a.as_string() + '"')

    def pp_bv(self, a):
        return to_format(a.as_string())

    def pp_fd(self, a):
        return to_format(a.as_string())

    def pp_fprm_value(self, a):
        _assert(cvc.is_fprm_value(a), "expected FPRMNumRef")
        ast_str = str(a.ast)
        if self.fpa_pretty:
            return to_format(_z3_fpa_rm_short_strings.get(ast_str))
        else:
            return to_format(_z3_fpa_rm_strings.get(ast_str))

    def pp_fp_value(self, a):
        _assert(isinstance(a, cvc.FPNumRef), "type mismatch")
        if not self.fpa_pretty:
            r = []
            if (a.isNaN()):
                r.append(to_format("fpNaN"))
                r.append(to_format("("))
                r.append(to_format(a.sort()))
                r.append(to_format(")"))
                return compose(r)
            elif (a.isInf()):
                if (a.isNegative()):
                    r.append(to_format("fpMinusInfinity"))
                else:
                    r.append(to_format("fpPlusInfinity"))
                r.append(to_format("("))
                r.append(to_format(a.sort()))
                r.append(to_format(")"))
                return compose(r)

            elif (a.isZero()):
                if (a.isNegative()):
                    return to_format("-zero")
                else:
                    return to_format("+zero")
            else:
                _assert(cvc.is_fp_value(a), "expecting FP num ast")
                r = []
                sgnb = a.sign()
                exp = a.exponent_as_long()
                sig = a.significand()
                if int(sig) == sig:
                    sig = int(sig)
                r.append(to_format("FPVal("))
                if sgnb and sgn.value != 0:
                    r.append(to_format("-"))
                r.append(to_format(sig))
                r.append(to_format("*(2**"))
                r.append(to_format(exp))
                r.append(to_format(", "))
                r.append(to_format(a.sort()))
                r.append(to_format("))"))
                return compose(r)
        else:
            if (a.isNaN()):
                return to_format("NaN")
            elif (a.isInf()):
                if (a.isNegative()):
                    return to_format("-oo")
                else:
                    return to_format("+oo")
            elif (a.isZero()):
                if (a.isNegative()):
                    return to_format("-0.0")
                else:
                    return to_format("+0.0")
            else:
                _assert(cvc.is_fp_value(a), "expecting FP num ast")
                r = []
                sgnb = a.sign()
                exp = a.exponent_as_long()
                sig = a.significand()
                if int(sig) == sig:
                    sig = int(sig)
                if sgnb:
                    r.append(to_format("-"))
                r.append(to_format(sig))
                if (str(exp) != "0"):
                    r.append(to_format("*(2**"))
                    r.append(to_format(exp))
                    r.append(to_format(")"))
                return compose(r)

    def pp_fp(self, a, d, xs):
        _assert(isinstance(a, cvc.FPRef), "type mismatch")
        k = a.kind()
        op = "?"
        if (self.fpa_pretty and k in _z3_op_to_fpa_pretty_str):
            op = _z3_op_to_fpa_pretty_str[k]
        elif k in _z3_op_to_fpa_normal_str:
            op = _z3_op_to_fpa_normal_str[k]
        elif k in _z3_op_to_str:
            op = _z3_op_to_str[k]

        n = a.num_args()

        if self.fpa_pretty:
            if self.is_infix(k) and n >= 3:
                rm = a.arg(0)
                if cvc.is_fprm_value(rm) and cvc.get_default_rounding_mode(a.ctx).eq(rm):
                    arg1 = to_format(self.pp_expr(a.arg(1), d + 1, xs))
                    arg2 = to_format(self.pp_expr(a.arg(2), d + 1, xs))
                    r = []
                    r.append(arg1)
                    r.append(to_format(" "))
                    r.append(to_format(op))
                    r.append(to_format(" "))
                    r.append(arg2)
                    return compose(r)
            elif k == Kind.FPNeg:
                return compose([to_format("-"), to_format(self.pp_expr(a.arg(0), d + 1, xs))])

        if k in _z3_op_to_fpa_normal_str:
            op = _z3_op_to_fpa_normal_str[k]

        r = []
        r.append(to_format(op))
        if not cvc.is_const(a):
            r.append(to_format("("))
            first = True
            for c in a.children():
                if first:
                    first = False
                else:
                    r.append(to_format(", "))
                r.append(self.pp_expr(c, d + 1, xs))
            r.append(to_format(")"))
            return compose(r)
        else:
            return to_format(a.as_string())

    def pp_prefix(self, a, d, xs):
        r = []
        sz = 0
        for child in a.children():
            r.append(self.pp_expr(child, d + 1, xs))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        return seq1(self.pp_name(a), r)

    def is_assoc(self, k):
        return _is_assoc(k)

    def is_left_assoc(self, k):
        return _is_left_assoc(k)

    def infix_args_core(self, a, d, xs, r):
        sz = len(r)
        k = a.kind()
        p = self.get_precedence(k)
        first = True
        for child in a.children():
            child_pp = self.pp_expr(child, d + 1, xs)
            child_k = None
            if cvc.is_app(child):
                child_k = child.kind()
            if k == child_k and (self.is_assoc(k) or (first and self.is_left_assoc(k))):
                self.infix_args_core(child, d, xs, r)
                sz = len(r)
                if sz > self.max_args:
                    return
            elif self.is_infix_unary(child_k):
                child_p = self.get_precedence(child_k)
                if (
                    p > child_p
                    or (_is_add(k) and _is_sub(child_k))
                    or (_is_sub(k) and first and _is_add(child_k))
                ):
                    r.append(child_pp)
                else:
                    r.append(self.add_paren(child_pp))
                sz = sz + 1
            # elif cvc.is_quantifier(child):
            #     r.append(self.add_paren(child_pp))
            else:
                r.append(child_pp)
                sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                return
            first = False

    def infix_args(self, a, d, xs):
        r = []
        self.infix_args_core(a, d, xs, r)
        return r

    def pp_infix(self, a, d, xs):
        k = a.kind()
        if self.is_infix_compact(k):
            op = self.pp_name(a)
            return group(seq(self.infix_args(a, d, xs), op, False))
        else:
            op = self.pp_name(a)
            sz = _len(op)
            op.string = " " + op.string
            op.size = sz + 1
            return group(seq(self.infix_args(a, d, xs), op))

    def pp_unary(self, a, d, xs):
        k = a.kind()
        p = self.get_precedence(k)
        child = a.children()[0]
        child_k = None
        if cvc.is_app(child):
            child_k = child.kind()
        child_pp = self.pp_expr(child, d + 1, xs)
        if k != child_k and self.is_infix_unary(child_k):
            child_p = self.get_precedence(child_k)
            if p <= child_p:
                child_pp = self.add_paren(child_pp)
        # if cvc.is_quantifier(child):
        #     child_pp = self.add_paren(child_pp)
        name = self.pp_name(a)
        return compose(to_format(name), indent(_len(name), child_pp))

    def pp_power_arg(self, arg, d, xs):
        r = self.pp_expr(arg, d + 1, xs)
        k = None
        if cvc.is_app(arg):
            k = arg.kind()
        if self.is_infix_unary(k) or (
            cvc.is_rational_value(arg) and arg.denominator_as_long() != 1
        ):
            return self.add_paren(r)
        else:
            return r

    def pp_power(self, a, d, xs):
        arg1_pp = self.pp_power_arg(a.arg(0), d + 1, xs)
        arg2_pp = self.pp_power_arg(a.arg(1), d + 1, xs)
        return group(seq((arg1_pp, arg2_pp), "**", False))

    def pp_neq(self):
        return to_format("!=")

    def pp_distinct(self, a, d, xs):
        if a.num_args() == 2:
            op = self.pp_neq()
            sz = _len(op)
            op.string = " " + op.string
            op.size = sz + 1
            return group(seq(self.infix_args(a, d, xs), op))
        else:
            return self.pp_prefix(a, d, xs)

    def pp_select(self, a, d, xs):
        if a.num_args() != 2:
            return self.pp_prefix(a, d, xs)
        else:
            arg1_pp = self.pp_expr(a.arg(0), d + 1, xs)
            arg2_pp = self.pp_expr(a.arg(1), d + 1, xs)
            return compose(
                arg1_pp, indent(2, compose(to_format("["), arg2_pp, to_format("]")))
            )

    def pp_unary_param(self, a, d, xs, param_on_right):
        p = a.ast.getOp().getIndices()
        arg = self.pp_expr(a.arg(0), d + 1, xs)
        if param_on_right:
            return seq1(self.pp_name(a), [arg, to_format(p)])
        else:
            return seq1(self.pp_name(a), [to_format(p), arg])

    def pp_extract(self, a, d, xs):
        h, l = a.ast.getOp().getIndices()
        arg = self.pp_expr(a.arg(0), d + 1, xs)
        return seq1(self.pp_name(a), [to_format(h), to_format(l), arg])

    def pp_loop(self, a, d, xs):
        l = Z3_get_decl_int_parameter(a.ctx_ref(), a.decl().ast, 0)
        arg = self.pp_expr(a.arg(0), d + 1, xs)
        if Z3_get_decl_num_parameters(a.ctx_ref(), a.decl().ast) > 1:
            h = Z3_get_decl_int_parameter(a.ctx_ref(), a.decl().ast, 1)
            return seq1("Loop", [arg, to_format(l), to_format(h)])
        return seq1("Loop", [arg, to_format(l)])

    def pp_set(self, id, a):
        return seq1(id, [self.pp_sort(a.sort())])

    def pp_pattern(self, a, d, xs):
        if a.num_args() == 1:
            return self.pp_expr(a.arg(0), d, xs)
        else:
            return seq1(
                "MultiPattern", [self.pp_expr(arg, d + 1, xs) for arg in a.children()]
            )

    def pp_is(self, a, d, xs):
        f = a.params()[0]
        return self.pp_fdecl(f, a, d, xs)

    def pp_map(self, a, d, xs):
        f = cvc.get_map_func(a)
        return self.pp_fdecl(f, a, d, xs)

    def pp_fdecl(self, f, a, d, xs):
        r = []
        sz = 0
        r.append(to_format(f.name()))
        for child in a.children():
            r.append(self.pp_expr(child, d + 1, xs))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        return seq1(self.pp_name(a), r)

    def pp_K(self, a, d, xs):
        return seq1(
            self.pp_name(a),
            [self.pp_sort(a.domain()), self.pp_expr(a.arg(0), d + 1, xs)],
        )

    def pp_atmost(self, a, d, f, xs):
        k = Z3_get_decl_int_parameter(a.ctx_ref(), a.decl().ast, 0)
        return seq1(
            self.pp_name(a),
            [seq3([self.pp_expr(ch, d + 1, xs) for ch in a.children()]), to_format(k)],
        )

    def pp_pbcmp(self, a, d, f, xs):
        chs = a.children()
        rchs = range(len(chs))
        k = Z3_get_decl_int_parameter(a.ctx_ref(), a.decl().ast, 0)
        ks = [Z3_get_decl_int_parameter(a.ctx_ref(), a.decl().ast, i + 1) for i in rchs]
        ls = [seq3([self.pp_expr(chs[i], d + 1, xs), to_format(ks[i])]) for i in rchs]
        return seq1(self.pp_name(a), [seq3(ls), to_format(k)])

    def pp_app(self, a, d, xs):
        if cvc.is_int_value(a):
            return self.pp_int(a)
        elif cvc.is_rational_value(a):
            return self.pp_rational(a)
        elif cvc.is_bool_value(a):
            return self.pp_bool(a)
        # elif cvc.is_algebraic_value(a):
        #     return self.pp_algebraic(a)
        elif cvc.is_bv_value(a):
            return self.pp_bv(a)
        elif cvc.is_fprm_value(a):
            return self.pp_fprm_value(a)
        elif cvc.is_fp_value(a):
            return self.pp_fp_value(a)
        elif cvc.is_fp(a):
            return self.pp_fp(a, d, xs)
        # elif cvc.is_string_value(a):
        #     return self.pp_string(a)
        elif cvc.is_const(a):
            return self.pp_const(a)
        else:
            k = a.kind()
            if k == Kind.Pow:
                return self.pp_power(a, d, xs)
            if k == Kind.Distinct:
                return self.pp_distinct(a, d, xs)
            elif k == Kind.Select:
                return self.pp_select(a, d, xs)
            elif k in [Kind.BVSignExtend, Kind.BVZeroExtend, Kind.BVRepeat]:
                return self.pp_unary_param(a, d, xs, False)
            elif k in [Kind.BVRotateLeft, Kind.BVRotateRight]:
                return self.pp_unary_param(a, d, xs, True)
            elif k == Kind.BVExtract:
                return self.pp_extract(a, d, xs)
            # elif k == Z3_OP_DT_IS:
            #     return self.pp_is(a, d, xs)
            # elif k == Z3_OP_ARRAY_MAP:
            #     return self.pp_map(a, d, xs)
            elif k == Kind.ConstArray:
                return self.pp_K(a, d, xs)
            # Slight hack to handle DT fns here (InternalKind case).
            elif k in [Kind.Constant, Kind.InternalKind, Kind.Variable, Kind.UninterpretedSortValue]:
                return self.pp_name(a)
            # elif k == Z3_OP_PB_AT_MOST:
            #     return self.pp_atmost(a, d, f, xs)
            # elif k == Z3_OP_PB_LE:
            #     return self.pp_pbcmp(a, d, f, xs)
            # elif k == Z3_OP_PB_GE:
            #     return self.pp_pbcmp(a, d, f, xs)
            # elif k == Z3_OP_PB_EQ:
            #     return self.pp_pbcmp(a, d, f, xs)
            # elif cvc.is_pattern(a):
            #     return self.pp_pattern(a, d, xs)
            elif self.is_infix(k):
                return self.pp_infix(a, d, xs)
            elif self.is_unary(k):
                return self.pp_unary(a, d, xs)
            elif k == Kind.ApplyUf:
                return self.pp_uf_apply(a, d, xs)
            elif k in [Kind.ApplyConstructor, Kind.ApplySelector, Kind.ApplyTester]:
                return self.pp_dt_apply(a, d, xs)
            else:
                return self.pp_prefix(a, d, xs)

    def pp_uf_apply(self, a, d, xs):
        r = []
        sz = 0
        first = a.decl()
        for child in a.children():
            r.append(self.pp_expr(child, d + 1, xs))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        return seq1(self.pp_name(first), r)

    def pp_dt_apply(self, a, d, xs):
        r = []
        sz = 0
        cs = a.children()
        for child in cs[1:]:
            r.append(self.pp_expr(child, d + 1, xs))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        if len(r) > 0:
            return seq1(self.pp_name(cs[0]), r)
        else:
            return self.pp_name(cs[0])

    def pp_var(self, a, d, xs):
        idx = cvc.get_var_index(a)
        sz = len(xs)
        if idx >= sz:
            return seq1("Var", (to_format(idx),))
        else:
            return to_format(xs[sz - idx - 1])

    def pp_quantifier(self, a, d, xs):
        ys = [to_format(a.var_name(i)) for i in range(a.num_vars())]
        new_xs = xs + ys
        body_pp = self.pp_expr(a.body(), d + 1, new_xs)
        if len(ys) == 1:
            ys_pp = ys[0]
        else:
            ys_pp = seq3(ys, "[", "]")
        if a.is_forall():
            header = "ForAll"
        elif a.is_exists():
            header = "Exists"
        else:
            header = "Lambda"
        return seq1(header, (ys_pp, body_pp))

    def pp_expr(self, a, d, xs):
        self.visited = self.visited + 1
        if d > self.max_depth or self.visited > self.max_visited:
            return self.pp_ellipses()
        # if cvc.is_var(a):
        #     return self.pp_var(a, d, xs)
        elif cvc.is_quantifier(a):
            return self.pp_quantifier(a, d, xs)
        elif cvc.is_app(a):
            return self.pp_app(a, d, xs)
        else:
            return to_format(self.pp_unknown())

    def pp_decl(self, f):
        k = f.kind()
        if k == Z3_OP_DT_IS or k == Z3_OP_ARRAY_MAP:
            g = f.params()[0]
            r = [to_format(g.name())]
            return seq1(self.pp_name(f), r)
        return self.pp_name(f)

    def pp_seq_core(self, f, a, d, xs):
        self.visited = self.visited + 1
        if d > self.max_depth or self.visited > self.max_visited:
            return self.pp_ellipses()
        r = []
        sz = 0
        for elem in a:
            r.append(f(elem, d + 1, xs))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        return seq3(r, "[", "]")

    def pp_seq(self, a, d, xs):
        return self.pp_seq_core(self.pp_expr, a, d, xs)

    def pp_seq_seq(self, a, d, xs):
        return self.pp_seq_core(self.pp_seq, a, d, xs)

    def pp_model(self, m):
        r = []
        sz = 0
        for d in m:
            i = m[d]
            if isinstance(i, cvc.FuncInterp):
                i_pp = self.pp_func_interp(i)
            else:
                i_pp = self.pp_expr(i, 0, [])
            name = self.pp_name(d)
            r.append(compose(name, to_format(" = "), indent(_len(name) + 3, i_pp)))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        return seq3(r, "[", "]")

    def pp_func_entry(self, e):
        num = e.num_args()
        if num > 1:
            args = []
            for i in range(num):
                args.append(self.pp_expr(e.arg_value(i), 0, []))
            args_pp = group(seq3(args))
        else:
            args_pp = self.pp_expr(e.arg_value(0), 0, [])
        value_pp = self.pp_expr(e.value(), 0, [])
        return group(seq((args_pp, value_pp), self.pp_arrow()))

    def pp_func_interp(self, f):
        r = []
        sz = 0
        num = f.num_entries()
        for i in range(num):
            r.append(self.pp_func_entry(f.entry(i)))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        if sz <= self.max_args:
            else_val = f.else_value()
            if else_val == None:
                else_pp = to_format("#unspecified")
            else:
                else_pp = self.pp_expr(else_val, 0, [])
            r.append(group(seq((to_format("else"), else_pp), self.pp_arrow())))
        return seq3(r, "[", "]")

    def pp_list(self, a):
        r = []
        sz = 0
        for elem in a:
            if _support_pp(elem):
                r.append(self.main(elem))
            else:
                r.append(to_format(str(elem)))
            sz = sz + 1
            if sz > self.max_args:
                r.append(self.pp_ellipses())
                break
        if isinstance(a, tuple):
            return seq3(r)
        else:
            return seq3(r, "[", "]")

    def main(self, a):
        if cvc.is_expr(a):
            return self.pp_expr(a, 0, [])
        elif cvc.is_sort(a):
            return self.pp_sort(a)
        elif cvc.is_func_decl(a):
            return self.pp_decl(a)
        elif isinstance(a, cvc.Solver):
            return self.pp_seq(a.assertions(), 0, [])
        elif isinstance(a, cvc.ModelRef):
            return self.pp_model(a)
        elif isinstance(a, list) or isinstance(a, tuple):
            return self.pp_list(a)
        else:
            return to_format(self.pp_unknown())

    def __call__(self, a):
        self.visited = 0
        return self.main(a)


_PP = PP()
_Formatter = Formatter()


def set_pp_option(k, v):
    if k == "fpa_pretty":
        if v:
            set_fpa_pretty(True)
        else:
            set_fpa_pretty(False)
        return True
    val = getattr(_PP, k, None)
    if val is not None:
        _assert(type(v) == type(val), "Invalid pretty print option value")
        setattr(_PP, k, v)
        return True
    val = getattr(_Formatter, k, None)
    if val is not None:
        _assert(type(v) == type(val), "Invalid pretty print option value")
        setattr(_Formatter, k, v)
        return True
    return False


def obj_to_string(a):
    out = io.StringIO()
    _PP(out, _Formatter(a))
    return out.getvalue()


def set_fpa_pretty(flag=True):
    global _Formatter
    global _z3_op_to_str
    _Formatter.fpa_pretty = flag
    if flag:
        for (_k, _v) in _z3_op_to_fpa_pretty_str.items():
            _z3_op_to_str[_k] = _v
        for _k in _z3_fpa_infix:
            _infix_map[_k] = True
    else:
        for (_k, _v) in _z3_op_to_fpa_normal_str.items():
            _z3_op_to_str[_k] = _v
        for _k in _z3_fpa_infix:
            _infix_map[_k] = False


set_fpa_pretty(True)


def get_fpa_pretty():
    global Formatter
    return _Formatter.fpa_pretty


def in_def_pp(a):
    if _support_pp(a):
        print(obj_to_string(a))
    else:
        print(a)


def print_matrix(m):
    _assert(isinstance(m, list) or isinstance(m, tuple), "matrix expected")
    print(obj_to_string(m))


def insert_line_breaks(s, width):
    """Break s in lines of size width (approx)"""
    sz = len(s)
    if sz <= width:
        return s
    new_str = io.StringIO()
    w = 0
    for i in range(sz):
        if w > width and s[i] == " ":
            new_str.write(u("<br />"))
            w = 0
        else:
            new_str.write(u(s[i]))
        w = w + 1
    return new_str.getvalue()
