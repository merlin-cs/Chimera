from __future__ import annotations

import random
from typing import NamedTuple, Union, Any
from snake_egg import EGraph, Rewrite, Var, vars
import sys

from src.parsing.Parse import parse_file, parse_str
from src.parsing.Ast import Const, Script, Term, Var, DeclareFun
from src.parsing.Types import *
from src.rewrite.equality_saturation.type_sys import *
from src.parsing.TimeoutDecorator import exit_after
from src.config.generator_loader import GENERATORS

Expr = Any



# covert Term to IR like "expr1 = Mul(Add(1, 'x'), Sub(1, 'x'))"
def convert_to_IR(term: Term) -> Any:
    if not isinstance(term, Term):
        return str(term)
    if term.op is None:
        # return str(term)
        if term.is_const:
            if term.name == "0":
                if random.choice([True, False]):
                    return Zero(AnyIntTerm())
            if term.name == "1":
                if random.choice([True, False]):
                    return One(AnyIntTerm())
            if term.name == "true":
                return TRUE(AnyBoolTerm())
            if term.name == "false":
                return FALSE(AnyBoolTerm())
        return str(term)
    # if isinstance(term, Var):
    #     return term.name
    if term.op == PLUS:
        # Add only supports 2 arguments
        if len(term.subterms) == 1:
            return convert_to_IR(term.subterms[0])
        elif len(term.subterms) == 2:
            return Add(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        else:
            temp = convert_to_IR(term.subterms[0])
            for subterm in term.subterms[1:]:
                temp = Add(temp, convert_to_IR(subterm))
            return temp

        # return Add(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == MINUS:
        if len(term.subterms) == 1:
            return Neg(convert_to_IR(term.subterms[0]))
        else:
            temp = convert_to_IR(term.subterms[0])
            for subterm in term.subterms[1:]:
                temp = Sub(temp, convert_to_IR(subterm))
            return temp
        # return Sub(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == MULTIPLY:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Mul(temp, convert_to_IR(subterm))
        return temp
        # return Mul(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == DIV:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = IntDiv(temp, convert_to_IR(subterm))
        return temp
        # return IntDiv(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == MOD:
        return Mod(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == ABS:
        return Abs(convert_to_IR(term.subterms[0]))
    if term.op == GTE:
        temp = Geq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        if len(term.subterms) > 2:
            for idx in range(1, len(term.subterms) - 1):
                temp = And(temp, Geq(convert_to_IR(term.subterms[idx]), convert_to_IR(term.subterms[idx + 1])))
        return temp
        # return Geq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == GT:
        temp = Gt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        if len(term.subterms) > 2:
            for idx in range(1, len(term.subterms) - 1):
                temp = And(temp, Gt(convert_to_IR(term.subterms[idx]), convert_to_IR(term.subterms[idx + 1])))
        return temp
        # return Gt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == LTE:
        temp = Leq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        if len(term.subterms) > 2:
            for idx in range(1, len(term.subterms) - 1):
                temp = And(temp, Leq(convert_to_IR(term.subterms[idx]), convert_to_IR(term.subterms[idx + 1])))
        return temp
        # return Leq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == LT:
        temp = Lt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        if len(term.subterms) > 2:
            for idx in range(1, len(term.subterms) - 1):
                temp = And(temp, Lt(convert_to_IR(term.subterms[idx]), convert_to_IR(term.subterms[idx + 1])))
        return temp
        # return Lt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == UNARY_MINUS:
        return Neg(convert_to_IR(term.subterms[0]))
    if term.op == ITE:
        return Ite(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == NOT:
        return Not(convert_to_IR(term.subterms[0]))
    if term.op == AND:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = And(temp, convert_to_IR(subterm))
        return temp
        # return And(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == OR:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Or(temp, convert_to_IR(subterm))
        return temp
        # return Or(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == IMPLIES:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Implies(temp, convert_to_IR(subterm))
        return temp
        # return Implies(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == XOR:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Xor(temp, convert_to_IR(subterm))
        return temp
        # return Xor(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == EQUAL:
        temp = Eq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
        for idx in range(1, len(term.subterms) - 1):
            temp = And(temp, Eq(convert_to_IR(term.subterms[idx]), convert_to_IR(term.subterms[idx + 1])))
        return temp
        # return Eq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == DISTINCT:
        return Distinct(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == REAL_DIV:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Div(temp, convert_to_IR(subterm))
        return temp
        # return Div(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == TO_REAL:
        return ToReal(convert_to_IR(term.subterms[0]))
    if term.op == TO_INT:
        return ToInt(convert_to_IR(term.subterms[0]))
    if term.op == IS_INT:
        return IsInt(convert_to_IR(term.subterms[0]))
    if term.op == CONCAT:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = Concat(temp, convert_to_IR(subterm))
        return temp
        # return Concat(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == STRLEN:
        return StrLen(convert_to_IR(term.subterms[0]))
    if term.op == STR_TO_INT:
        return StrToInt(convert_to_IR(term.subterms[0]))
    if term.op == STR_AT:
        return StrAt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == STR_SUBSTR:
        return StrSubstr(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == LEXORD:
        return StrLt(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == REFLEX_CLOS:
        return StrLeq(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == STR_PREFIXOF:
        return StrPrefixof(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == STR_SUFFIXOF:
        return StrSuffixof(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == STR_CONTAINS:
        return StrContains(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == STR_INDEXOF:
        return StrIndexof(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == STR_REPLACE:
        return StrReplace(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == STR_REPLACE_ALL:
        return StrReplaceAll(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == STR_REPLACE_RE:
        return StrReplaceRe(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == STR_REPLACE_RE_ALL:
        return StrReplaceReAll(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]), convert_to_IR(term.subterms[2]))
    if term.op == STR_IS_DIGIT:
        return StrIsDigit(convert_to_IR(term.subterms[0]))
    if term.op == STR_TO_CODE:
        return StrToCode(convert_to_IR(term.subterms[0]))
    if term.op == STR_FROM_CODE:
        return StrFromCode(convert_to_IR(term.subterms[0]))
    if term.op == STR_FROM_INT:
        return StrFromInt(convert_to_IR(term.subterms[0]))
    if term.op == STR_TO_RE:
        return StrToRe(convert_to_IR(term.subterms[0]))
    if term.op == STR_IN_RE:
        return StrInRe(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == RE_NONE:
        return ReNone()
    if term.op == RE_ALL:
        return ReAll()
    if term.op == RE_ALLCHAR:
        return ReAllChar()
    if term.op == RE_CONCAT:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = ReConcat(temp, convert_to_IR(subterm))
        return temp
        # return ReConcat(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == RE_UNION:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = ReUnion(temp, convert_to_IR(subterm))
        return temp
        # return ReUnion(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == RE_INTER:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = ReIntersect(temp, convert_to_IR(subterm))
        return temp
        # return ReIntersect(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == RE_KLENE:
        return ReStar(convert_to_IR(term.subterms[0]))
    if term.op == RE_PLUS:
        return RePlus(convert_to_IR(term.subterms[0]))
    if term.op == RE_OPT:
        return ReOpt(convert_to_IR(term.subterms[0]))
    if term.op == RE_RANGE:
        return ReRange(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == RE_COMP:
        return ReComp(convert_to_IR(term.subterms[0]))
    if term.op == RE_DIFF:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = ReDiff(temp, convert_to_IR(subterm))
        return temp
        # return ReDiff(convert_to_IR(term.subterms[0]), convert_to_IR(term.subterms[1]))
    if term.op == BV_CONCAT:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvConcat(temp, convert_to_IR(subterm))
        return temp
        # return BvConcat(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == BVNOT:
        return BvNot(convert_to_IR(term.subterms[0]))
    if term.op == BVNEG:
        return BvNeg(convert_to_IR(term.subterms[0]))
    if term.op == BVAND:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvAnd(temp, convert_to_IR(subterm))
        return temp
        # return BvAnd(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == BVOR:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvOr(temp, convert_to_IR(subterm))
        return temp
        # return BVOr(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == BVXOR:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvXor(temp, convert_to_IR(subterm))
        return temp
        # return BVXor(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op == BVADD:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvAdd(temp, convert_to_IR(subterm))
        return temp
    if term.op == BVSUB:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvSub(temp, convert_to_IR(subterm))
        return temp
    if term.op == BVMUL:
        temp = convert_to_IR(term.subterms[0])
        for subterm in term.subterms[1:]:
            temp = BvMul(temp, convert_to_IR(subterm))
        return temp
        # return BVMul(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVUDIV:
    #     return BVUDiv(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVUREM:
    #     return BVURem(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVSHL:
    #     return BVShl(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVLSHR:
    #     return BVLShr(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVASHR:
    #     return BVAshr(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVULT:
    #     return BVUlt(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVULE:
    #     return BVUle(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVSLT:
    #     return BVSlt(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVSGT:
    #     return BVSgt(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op == BVSDIV:
    #     return BVSdiv(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op.startswith(BV_EXTRACT):
    #     return BVExtract(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op.startswith(BV_ZERO_EXTEND):
    #     return BVZeroExtend(*[convert_to_IR(arg) for arg in term.subterms])
    # if term.op.startswith(BV_SIGN_EXTEND):
    #     return BVSignExtend(*[convert_to_IR(arg) for arg in term.subterms])
    # Add more operators as needed
    # return Other(*[convert_to_IR(arg) for arg in term.subterms])
    if term.op:
        if term.subterms is None or len(term.subterms) == 0:
            return str(term)
        elif len(term.subterms) == 1:
            return Other(term.op, convert_to_IR(term.subterms[0]), "")
        else:
            temp = convert_to_IR(term.subterms[0])
            for subterm in term.subterms[1:]:
                temp = Other(term.op, temp, convert_to_IR(subterm))
            return temp
    return str(term)


def convert_IR_to_str(ir: Any) -> str:
    if isinstance(ir, Add):
        return f"(+ {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Sub):
        return f"(- {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Mul):
        return f"(* {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Div):
        return f"(/ {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Mod):
        return f"(mod {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, IntDiv):
        return f"(div {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Abs):
        return f"(abs {convert_IR_to_str(ir.x)})"
    if isinstance(ir, Geq):
        return f"(>= {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Gt):
        return f"(> {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Leq):
        return f"(<= {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Lt):
        return f"(< {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Neg):
        return f"(- {convert_IR_to_str(ir.x)})"
    if isinstance(ir, Ite):
        return f"(ite {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, Not):
        return f"(not {convert_IR_to_str(ir.x)})"
    if isinstance(ir, And):
        return f"(and {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Or):
        return f"(or {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Implies):
        return f"(=> {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Xor):
        return f"(xor {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Eq):
        return f"(= {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Distinct):
        return f"(distinct {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ToReal):
        return f"(to_real {convert_IR_to_str(ir.x)})"
    if isinstance(ir, ToInt):
        return f"(to_int {convert_IR_to_str(ir.x)})"
    if isinstance(ir, IsInt):
        return f"(is_int {convert_IR_to_str(ir.x)})"
    if isinstance(ir, Concat):
        return f"(str.++ {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrLen):
        return f"(str.len {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrToRe):
        return f"(str.to_re {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrInRe):
        return f"(str.in_re {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ReNone):
        return "re.none"
    if isinstance(ir, ReAll):
        return "re.all"
    if isinstance(ir, ReAllChar):
        return "re.allchar"
    if isinstance(ir, ReConcat):
        return f"(re.++ {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ReUnion):
        return f"(re.union {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ReIntersect):
        return f"(re.inter {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ReStar):
        return f"(re.* {convert_IR_to_str(ir.x)})"
    if isinstance(ir, RePlus):
        return f"(re.+ {convert_IR_to_str(ir.x)})"
    if isinstance(ir, ReOpt):
        return f"(re.opt {convert_IR_to_str(ir.x)})"
    if isinstance(ir, ReRange):
        return f"(re.range {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, ReComp):
        return f"(re.comp {convert_IR_to_str(ir.x)})"
    if isinstance(ir, ReDiff):
        return f"(re.diff {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrAt):
        return f"(str.at {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrSubstr):
        return f"(str.substr {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrLt):
        return f"(str.< {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrLeq):
        return f"(str.<= {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrPrefixof):
        return f"(str.prefixof {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrSuffixof):
        return f"(str.suffixof {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrContains):
        return f"(str.contains {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, StrIndexof):
        return f"(str.indexof {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrReplace):
        return f"(str.replace {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrReplaceAll):
        return f"(str.replace_all {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrReplaceRe):
        return f"(str.replace_re {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrReplaceReAll):
        return f"(str.replace_re_all {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)} {convert_IR_to_str(ir.z)})"
    if isinstance(ir, StrIsDigit):
        return f"(str.is_digit {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrToCode):
        return f"(str.to_code {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrFromCode):
        return f"(str.from_code {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrToInt):
        return f"(str.to_int {convert_IR_to_str(ir.x)})"
    if isinstance(ir, StrFromInt):
        return f"(str.from_int {convert_IR_to_str(ir.x)})"
    # if isinstance(ir, TRUE) or ir == TRUE:
    #     return "true"
    # if isinstance(ir, FALSE) or ir == FALSE:
    #     return "false"
    if isinstance(ir, EmptyString) or ir == EmptyString:
        return '\"\"'
    if isinstance(ir, BvConcat):
        return f"(concat {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvNot):
        return f"(bvnot {convert_IR_to_str(ir.x)})"
    if isinstance(ir, BvNeg):
        return f"(bvneg {convert_IR_to_str(ir.x)})"
    if isinstance(ir, BvAnd):
        return f"(bvand {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvOr):
        return f"(bvor {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvXor):
        return f"(bvxor {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvAdd):
        return f"(bvadd {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvSub):
        return f"(bvsub {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, BvMul):
        return f"(bvmul {convert_IR_to_str(ir.x)} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Extract):
        return f"(extract {ir.x} {ir.y} {convert_IR_to_str(ir.z)})"
    # if isinstance(ir, BvZeroExtend):
    #     return f"(zero_extend {ir.x} {convert_IR_to_str(ir.y)})"
    # if isinstance(ir, BvSignExtend):
    #     return f"(sign_extend {ir.x} {convert_IR_to_str(ir.y)})"
    if isinstance(ir, Other):
        return f"({ir.symbol} {convert_IR_to_str(ir.arg1)} {convert_IR_to_str(ir.arg2)})"
    if ir is Zero or isinstance(ir, Zero):
        return "0"
    if ir is One or isinstance(ir, One):
        return "1"
    if ir is AnyIntTerm or isinstance(ir, AnyIntTerm):
        return "any_int"
    if ir is AnyBoolTerm or isinstance(ir, AnyBoolTerm):
        return "any_bool"
    if ir is TRUE or isinstance(ir, TRUE) or ir == TRUE:
        return "true"
    if ir is FALSE or isinstance(ir, FALSE) or ir == FALSE:
        return "false"
    
    return str(ir)
    

a, b, c, d, e, f = vars("a b c d e f")



ARITH_RULES = [
    Rewrite(Add(a, b), Add(b, a), "commute-add"),
    Rewrite(Mul(a, b), Mul(b, a), "commute-mul"),
    Rewrite(Add(a, 0), a, "add-0"),
    Rewrite(Mul(a, 0), 0, "mul-0"),
    Rewrite(Mul(a, 1), a, "mul-1"),
    # Rewrite(Add(a, 0, b), Add(a, b), "add-zero"),
    Rewrite(Add(a, b), Add(Add(a, 0), b), "add-zero"),
    # Rewrite(Mul(a, 1, b), Mul(a, b), "mul-one"),
    Rewrite(Mul(a, b), Mul(Mul(a, 1), b), "mul-one"),
    # Rewrite(Mul(a, 0, b), 0, "mul-zero"),
    Rewrite(Gt(a, b), Not(Leq(a, b)), "gt-to-not-leq"),
    Rewrite(Lt(a, b), Not(Geq(a, b)), "lt-to-not-geq"),
    Rewrite(Gt(a, b), Geq(a, Add(b, 1)), "gt-to-geq-add1"),
    Rewrite(Lt(a, b), Geq(b, Add(a, 1)), "lt-to-geq-add1"),
    Rewrite(Leq(a, b), Geq(b, a), "leq-to-geq"),
    Rewrite(Leq(a, b), Not(Geq(a, Add(b, 1))), "leq-to-not-geq-add1"),
    Rewrite(Not(Geq(a, b)), Geq(b, Add(a, 1)), "not-geq-to-geq-add1"),
    Rewrite(Geq(a, b), Geq(Sub(a, b), 0), "geq-to-sub-geq0"),
    Rewrite(Geq(a, b), Leq(Neg(a), Neg(b)), "geq-to-leq-neg"),
    Rewrite(Leq(a, a), TRUE(a), "leq-same-true"),
    Rewrite(Lt(a, a), FALSE(a), "lt-same-false"),
    Rewrite(Geq(a, a), TRUE(a), "geq-same-true"),
    Rewrite(Gt(a, a), FALSE(a), "gt-same-false"),
    # Rewrite(Eq(a, b), And(Geq(a, b), Leq(a, b)), "eq-to-geq-leq"),
    # Rewrite(Add(a, Add(b, c)), Add(a, b, c), "flatten-add"),
    # Rewrite(Mul(a, Mul(b, c)), Mul(a, b, c), "flatten-mul"),
    Rewrite(Mul(a, Add(b, c)), Add(Mul(a, b), Mul(a, c)), "distribute-mul-over-add"),
    # Rewrite(Mul(Add(a, b), Sub(a, b)), Sub(Mul(a, a), Mul(b, b)), "difference-of-squares"),
    Rewrite(Abs(a), Ite(Lt(a, 0), Neg(a), a), "abs-to-ite"),
    # Rewrite(ToReal(a), a, "to-real-eliminate"),
    Rewrite(ToInt(ToReal(a)), ToInt(a), "to-int-to-real-simplify"),
    Rewrite(Div(ToReal(a), b), Div(a, b), "div-to-real-eliminate"),
    # Rewrite(Div(a, ToReal(b)), Div(a, b), "div-to-real-eliminate"),
    Rewrite(Div(a, b), Div(a, ToReal(b)), "re-div-to-real-eliminate"),
    Rewrite(Zero(a), Sub(a, a), "zero-from-sub-self"),
    Rewrite(Zero(a), Add(a, Neg(a)), "zero-from-add-neg"),
    Rewrite(Zero(a), Mul(a, 0), "zero-from-mul-zero"),
    Rewrite(Zero(a), Mod(a, 1), "zero-from-mod-one"),
    Rewrite(One(a), IntDiv(a, a), "one-from-int-div-self"),
    Rewrite(One(a), Div(a, a), "one-from-div-self"),
    ]

ARITH_ADDITIONAL_RULES = [
    # Maintained and made safe
    Rewrite(Eq(Concat(a, b), b), Eq(a, EmptyString()), "concat-c-eq-c-to-eq-empty"),
    Rewrite(Ite(Eq(b, 0), 0, IntDiv(Mod(a, b), b)), 0, "ite-div-mod-zero"),
    Rewrite(ToInt(ToReal(a)), ToInt(a), "toint-toreal"),
    Rewrite(ToInt(a), ToInt(ToReal(a)), "toreal-toint-reverse"),
    Rewrite(Mul(a, Mul(b, c)), Mul(b, Mul(a, c)), "mul-reorder"),
    Rewrite(Abs(Sub(a, b)), Abs(Sub(b, a)), "abs-sub-swap"),
    Rewrite(Abs(Mul(a, b)), Mul(Abs(a), Abs(b)), "abs-mul-to-mul-abs"),
    Rewrite(Mul(Abs(a), Abs(b)), Abs(Mul(a, b)), "mul-abs-to-abs-mul"),
    Rewrite(Abs(Abs(a)), Abs(a), "abs-abs-to-abs"),
    Rewrite(Abs(Mul(a, a)), Mul(a, a), "abs-square-to-square"),

    # Bidirectional rules for Sub/Add/Mul
    Rewrite(Sub(a, Sub(b, c)), Sub(c, Sub(b, a)), "sub-switch-sides"),
    Rewrite(Sub(c, Sub(b, a)), Sub(a, Sub(b, c)), "sub-switch-sides-reverse"),
    Rewrite(Sub(Sub(a, b), c), Sub(Sub(a, c), b), "sub-assoc-switch"),
    Rewrite(Sub(Sub(a, c), b), Sub(Sub(a, b), c), "sub-assoc-switch-reverse"),
    Rewrite(Add(a, Add(b, c)), Add(b, Add(a, c)), "add-reorder"),
    Rewrite(Sub(Add(a, b), c), Add(b, Sub(a, c)), "sub-add-to-add-sub"),
    Rewrite(Add(b, Sub(a, c)), Sub(Add(a, b), c), "add-sub-to-sub-add"),
    Rewrite(Mul(a, Sub(b, c)), Mul(Neg(a), Sub(c, b)), "mul-neg-switch"),
    Rewrite(Add(a, Sub(b, Add(a, c))), Sub(b, c), "add-const-sub-add-const-to-sub"),
    Rewrite(Sub(Mul(a, b), Mul(b, c)), Mul(b, Sub(a, c)), "sub-mul-to-mul-sub"),
    Rewrite(Mul(b, Sub(a, c)), Sub(Mul(a, b), Mul(b, c)), "mul-sub-to-sub-mul"),
    Rewrite(Add(Mul(a, b), Mul(b, c)), Mul(b, Add(a, c)), "add-mul-to-mul-add"),
    Rewrite(Mul(b, Add(a, c)), Add(Mul(a, b), Mul(b, c)), "mul-add-to-add-mul"),

    # Bidirectional difference of squares
    Rewrite(Sub(Mul(a, a), Mul(b, b)), Mul(Sub(a, b), Add(a, b)), "difference-of-squares"),
    Rewrite(Mul(Sub(a, b), Add(a, b)), Sub(Mul(a, a), Mul(b, b)), "product-to-difference-of-squares"),

    # Additional algebraic identities
    Rewrite(Sub(a, b), Add(a, Neg(b)), "sub-to-add-neg"),
    Rewrite(Add(a, Neg(b)), Sub(a, b), "add-neg-to-sub"),
    Rewrite(Sub(a, b), Neg(Sub(b, a)), "sub-swap-neg"),
    Rewrite(Neg(Sub(b, a)), Sub(a, b), "neg-sub-swap"),
    Rewrite(Div(Add(a, b), c), Add(Div(a, c), Div(b, c)), "distribute-div-over-add"),
    Rewrite(Add(Div(a, c), Div(b, c)), Div(Add(a, b), c), "factor-div-over-add"),

    # Symbolic generation rules (safe)
    Rewrite(Zero(a), Ite(Eq(a, 0), 0, Mul(a, Div(0, a))), "zero-from-ite-mul-div-zero"),
    Rewrite(Zero(a), Ite(Eq(a, 0), 0, Mul(a, IntDiv(0, a))), "zero-from-ite-mul-intdiv-zero"),
    Rewrite(One(a), Ite(Eq(a, 0), 1, Div(a, a)), "one-from-div-self-safe"),
    Rewrite(One(a), Ite(Eq(a, 0), 1, IntDiv(a, a)), "one-from-intdiv-self-safe"),

    # Safe ITE rules
    Rewrite(Ite(Eq(a, 0), Mul(a, b), Mul(a, Mul(b, Div(a, a)))), Mul(a, b), "ite-mul-div-one"),
    Rewrite(Ite(Eq(a, 0), Mul(a, b), Mul(a, Mul(b, IntDiv(a, a)))), Mul(a, b), "ite-mul-intdiv-one"),
    Rewrite(Ite(Eq(a, 0), Mul(a, b), Div(Mul(a, b), Div(a, a))), Mul(a, b), "ite-div-div-cancel"),
    Rewrite(Ite(Eq(a, 0), Mul(a, b), IntDiv(Mul(a, b), IntDiv(a, a))), Mul(a, b), "ite-intdiv-div-cancel"),
    Rewrite(Ite(Eq(Sub(a, b), 0), Div(Sub(b, a), Sub(a, b)), Div(Sub(a, b), Sub(b, a))), Div(Sub(b, a), Sub(a, b)), "ite-div-swap"),
    Rewrite(Ite(Eq(Sub(a, b), 0), IntDiv(Sub(b, a), Sub(a, b)), IntDiv(Sub(a, b), Sub(b, a))), IntDiv(Sub(b, a), Sub(a, b)), "ite-intdiv-swap"),
    Rewrite(Ite(Eq(Sub(b, a), 0), Div(Sub(b, a), Sub(b, a)), Div(Sub(a, b), Sub(a, b))), Div(Sub(b, a), Sub(b, a)), "ite-div-swap-zero"),
    Rewrite(Ite(Eq(Sub(b, a), 0), IntDiv(Sub(b, a), Sub(b, a)), IntDiv(Sub(a, b), Sub(a, b))), IntDiv(Sub(b, a), Sub(b, a)), "ite-intdiv-swap-zero"),
    Rewrite(Ite(Eq(Sub(b, a), 0), Div(0, Sub(b, a)), Div(0, Sub(a, b))), Div(0, Sub(b, a)), "ite-zero-div-simplify"),
    Rewrite(Ite(Eq(Sub(b, a), 0), IntDiv(0, Sub(b, a)), IntDiv(0, Sub(a, b))), IntDiv(0, Sub(b, a)), "ite-zero-intdiv-simplify"),
    Rewrite(Ite(Eq(a, 0), Div(Abs(a), a), Div(a, Abs(a))), Div(Abs(a), a), "ite-div-abs-over-x"),
    Rewrite(Ite(Eq(a, 0), IntDiv(Abs(a), a), IntDiv(a, Abs(a))), IntDiv(Abs(a), a), "ite-intdiv-abs-over-x"),
    Rewrite(Ite(Eq(a, 0), Div(a, Abs(a)), Div(Abs(a), a)), Div(a, Abs(a)), "ite-div-x-over-abs-x"),
    Rewrite(Ite(Eq(a, 0), IntDiv(a, Abs(a)), IntDiv(Abs(a), a)), IntDiv(a, Abs(a)), "ite-intdiv-x-over-abs-x"),
    Rewrite(Ite(Eq(a, 0), Div(a, a), Div(Abs(a), Abs(a))), Div(a, a), "ite-div-x-over-x"),
    Rewrite(Ite(Eq(a, 0), IntDiv(a, a), IntDiv(Abs(a), Abs(a))), IntDiv(a, a), "ite-intdiv-x-over-x"),
    Rewrite(Ite(Eq(a, 0), Div(Abs(a), Neg(a)), Div(Neg(a), Abs(a))), Div(Abs(a), Neg(a)), "ite-div-abs-over-neg-x"),
    Rewrite(Ite(Eq(a, 0), IntDiv(Abs(a), Neg(a)), IntDiv(Neg(a), Abs(a))), IntDiv(Abs(a), Neg(a)), "ite-intdiv-abs-over-neg-x"),
    Rewrite(Ite(Eq(a, 0), Div(Neg(a), Abs(a)), Div(Abs(a), Neg(a))), Div(Neg(a), Abs(a)), "ite-div-neg-x-over-abs-x"),
    Rewrite(Ite(Eq(a, 0), IntDiv(Neg(a), Abs(a)), IntDiv(Abs(a), Neg(a))), IntDiv(Neg(a), Abs(a)), "ite-intdiv-neg-x-over-abs-x"),
]

CORE_RULES = [
    # Foundational Boolean Identities (Bidirectional)
    Rewrite(Not(Not(a)), a, "double-not-elim"),
    # Rewrite(a, Not(Not(a)), "double-not-intro"),

    # Implication and Disjunction Equivalences (Bidirectional)
    Rewrite(Implies(a, b), Or(Not(a), b), "implies-to-or"),
    Rewrite(Or(Not(a), b), Implies(a, b), "or-to-implies"),
    Rewrite(Not(Implies(a, b)), And(a, Not(b)), "not-implies-to-and"),
    Rewrite(And(a, Not(b)), Not(Implies(a, b)), "and-to-not-implies"),

    # De Morgan's Laws (Bidirectional)
    Rewrite(Not(And(a, b)), Or(Not(a), Not(b)), "demorgan-and"),
    Rewrite(Or(Not(a), Not(b)), Not(And(a, b)), "demorgan-and-reverse"),
    Rewrite(Not(Or(a, b)), And(Not(a), Not(b)), "demorgan-or"),
    Rewrite(And(Not(a), Not(b)), Not(Or(a, b)), "demorgan-or-reverse"),

    # Identity Introduction/Elimination
    # Rewrite(a, And(a, TRUE()), "and-true-intro"),
    Rewrite(And(a, TRUE()), a, "and-true-elim"),
    # Rewrite(a, Or(a, FALSE()), "or-false-intro"),
    Rewrite(Or(a, FALSE()), a, "or-false-elim"),

    # XOR and Equivalence (Bidirectional)
    Rewrite(Not(Xor(a, b)), Eq(a, b), "not-xor-to-eq"),
    # Rewrite(Eq(a, b), Not(Xor(a, b)), "eq-to-not-xor"),
    Rewrite(Xor(a, b), Not(Eq(a, b)), "xor-to-not-eq"),
    # Rewrite(Not(Eq(a, b)), Xor(a, b), "not-eq-to-xor"),

    # Symbolic TRUE Generation from Tautologies
    Rewrite(TRUE(a), Or(a, Not(a)), "symbolic-true-from-or"),
    Rewrite(TRUE(a), Eq(a, a), "symbolic-true-from-eq"),
    Rewrite(TRUE(a), Xor(a, Not(a)), "symbolic-true-from-xor"),

    # Symbolic FALSE Generation from Contradictions
    Rewrite(FALSE(a), And(a, Not(a)), "symbolic-false-from-and"),
    Rewrite(FALSE(a), Xor(a, a), "symbolic-false-from-xor"),
    Rewrite(FALSE(a), Eq(a, Not(a)), "symbolic-false-from-eq-not"),

    # Core Simplification Rules (Mainly Unidirectional)
    Rewrite(Implies(FALSE(), a), TRUE(a), "false-implies"),
    Rewrite(Implies(a, TRUE()), TRUE(a), "implies-true"),
    Rewrite(Implies(TRUE(), a), a, "true-implies"),
    Rewrite(Or(a, TRUE()), TRUE(a), "or-true"),
    Rewrite(And(a, FALSE()), FALSE(a), "and-false"),
    Rewrite(Xor(a, FALSE()), a, "xor-false"),
    Rewrite(Xor(a, TRUE()), Not(a), "xor-true"),
    Rewrite(Eq(a, TRUE()), a, "eq-true"),
    Rewrite(Eq(a, FALSE()), Not(a), "eq-false"),
]

STRING_RULES = [
    Rewrite(Eq(Concat(Concat(a, b), c), d), FALSE(), "eq-string_concat-false"),
    # Rewrite(Eq(a, b), FALSE(), "eq-false"),
    # Rewrite(Concat(a, Concat(b, c), d), Concat(a, b, c, d), "string_concat-assoc"),
    Rewrite(Eq(Concat(Concat(a, b), c), d), Eq(d, Concat(Concat(a, b), c)), "eq-string_concat-reorder"),
    Rewrite(Eq(Concat(a, Concat(b, c)), d), Eq(d, Concat(Concat(a, b), c)), "eq-string_concat-reorder-2"),
    Rewrite(StrSubstr(EmptyString(), a, b), EmptyString(), "substr-empty-string"),
    Rewrite(StrSubstr(a, b, c), EmptyString(), "substr-empty"),
    Rewrite(Eq(StrSubstr(a, b, c), ""), Eq(a, ""), "substr-eq-empty"),
    Rewrite(StrLen(StrReplace(a, b, c)), StrLen(a), "length-replace"),
    # Rewrite(StrLen(StringUpdate(a, b, c)), StrLen(a), "length-update"),
    Rewrite(StrLen(StrSubstr(a, b, c)), c, "length-substr"),
    Rewrite(Geq(a, StrLen(StrSubstr(b, c, d))), TRUE(a), "geq-length-substr"),
    Rewrite(Eq(Concat(a, b), Concat(c, d)), FALSE(a), "concat-eq-false"),
    Rewrite(Eq(a, Concat(b, c)), FALSE(a), "eq-concat-false"),
    Rewrite(Eq(Concat(Concat(a, b), c), Concat(Concat(a, d), e)), Eq(Concat(b, c), Concat(d, e)), "concat-eq-elim"),
    # Rewrite(Eq(Concat(Concat(a, b), c), Concat(d, e, c)), Eq(Concat(a, b), Concat(d, e)), "concat-eq-elim"),
    Rewrite(Eq(a, Concat(a, b)), Eq(EmptyString(), b), "concat-eq-cancel"),
    # Rewrite(Eq(a, Concat(b, c, a)), Eq("", Concat(b, c)), "concat-eq-cancel"),
    Rewrite(Eq(Concat(Concat(a, b), c), Concat(Concat(d, e), f)), FALSE(), "concat-eq-false-2"),
    Rewrite(Eq(Concat(a, Concat(b, c)), Concat(d, Concat(e, f))), FALSE(), "concat-eq-false-3"),
    Rewrite(StrPrefixof(a, b), Eq(a, StrSubstr(b, 0, StrLen(a))), "prefix-to-substr"),
    Rewrite(StrSuffixof(a, b), Eq(a, StrSubstr(b, Sub(StrLen(b), StrLen(a)), StrLen(a))), "suffix-to-substr"),
    Rewrite(StrPrefixof(a, b), StrContains(b, a), "prefix-to-contains"),
    Rewrite(StrSuffixof(a, b), StrContains(b, a), "suffix-to-contains"),
    Rewrite(StrSubstr(StrSubstr(a, b, c), d, e), StrSubstr(a, Add(b, d), Sub(c, d)), "substr-of-substr1"),
    Rewrite(StrSubstr(StrSubstr(a, b, c), d, e), StrSubstr(a, Add(b, d), e), "substr-of-substr2"),
    Rewrite(StrSubstr(StrSubstr(a, b, c), d, e), StrSubstr(a, Add(b, d), e), "substr-of-substr3"),
    Rewrite(StrSubstr(StrSubstr(a, b, c), d, e), StrSubstr(a, Add(b, d), Sub(c, d)), "substr-of-substr4"),
    Rewrite(StrSubstr(Concat(a, b), c, d), StrSubstr(a, c, d), "substr-of-concat3"),
    Rewrite(StrSubstr(Concat(Concat(a, b), c), d, e), StrSubstr(Concat(b, c), Sub(d, StrLen(a)), e), "substr-of-concat"),
    Rewrite(StrSubstr(a, 0, b), a, "substr-zero-start"),
    Rewrite(StrContains(a, a), TRUE(a), "contains-self"),
    Rewrite(StrContains(Concat(Concat(a, b), c), d), TRUE(a), "contains-in-concat1"),
    Rewrite(StrContains(Concat(Concat(a, b), c), d), Or(StrContains(a, d), StrContains(Concat(b, c), d)), "contains-in-concat2"),
    # Rewrite(StrContains(a, b), FALSE(), "contains-false"),
    # Rewrite(StrContains(a, b), Eq(a, b), "contains-eq"),
    # Rewrite(StrContains(a, b), TRUE(), "contains-true"),
    # Rewrite(Concat(Concat(a, EmptyString()), c), Concat(a, b), "concat-empty-string"),
    Rewrite(StrAt(a, b), StrSubstr(a, b, 1), "at-to-substr"),
    Rewrite(StrReplace(a, a, b), b, "replace-self"),
    Rewrite(StrReplace(Concat(a, b), a, c), Concat(c, b), "replace-in-concat"),
    # Rewrite(StrReplace(a, b, c), a, "replace-no-match"),
    # Rewrite(StrReplace(a, "", b), Concat(b, a), "replace-empty-pattern"),
    Rewrite(StrReplace(Concat(a, b), c, d), Concat(StrReplace(a, c, d), b), "replace-in-concat2"),
    # Rewrite(StrReplaceAll(a, b, c), a, "replace-all-no-match"),
    Rewrite(StrReplaceRe(a, ReNone(), b), a, "replace-re-none"),
    Rewrite(StrReplaceReAll(a, ReNone(), b), a, "replace-re-all-none"),
    Rewrite(StrLen(Concat(Concat(a, b), c)), StrLen(Concat(b, c)), "length-of-concat"),
    # Rewrite(StrIndexof(a, a, b), StrIndexof("", "", b), "indexof-self"),
    # Rewrite(StrIndexof(a, b, c), Neg(1), "indexof-no-match"),
    Rewrite(StrIndexof(Concat(a, b), c, d), StrIndexof(a, c, d), "indexof-in-concat"),
    # Rewrite(StrIndexofRe(a, ReNone(), b), Neg(1), "indexof-re-none"),
    # Rewrite(StringToLower(Concat(Concat(a, b), c)), StringToLower(Concat(b, c)), "tolower-of-concat"),
    # Rewrite(StringToUpper(Concat(Concat(a, b), c)), StringToUpper(Concat(b, c)), "toupper-of-concat"),
    # Rewrite(StringToLower(StringToUpper(a)), StringToLower(a), "tolower-toupper"),
    # Rewrite(StringToUpper(StringToLower(a)), StringToUpper(a), "toupper-tolower"),
    # Rewrite(StrLen(StringToLower(a)), StrLen(a), "length-tolower"),
    # Rewrite(StrLen(StringToUpper(a)), StrLen(a), "length-toupper"),
    # Rewrite(StringToLower(StringIToS(a)), StringIToS(a), "tolower-itos"),
    # Rewrite(StringToUpper(StringIToS(a)), StringIToS(a), "toupper-itos"),
    # Rewrite(StringSToI(Concat(Concat(a, b), c)), Neg(1), "stoi-concat"),
    # Rewrite(StrLeq("", a), TRUE(), "leq-empty-left"),
    # Rewrite(StrLeq(a, ""), Eq(a, ""), "leq-empty-right"),
    Rewrite(StrLeq(Concat(Concat(a, b), c), Concat(Concat(a, d), e)), FALSE(a), "leq-concat-false"),
    Rewrite(StrLeq(Concat(Concat(a, b), c), Concat(Concat(a, d), e)), TRUE(a), "leq-concat-true"),
    Rewrite(StrLt(a, b), And(Not(Eq(a, b)), StrLeq(a, b)), "lt-to-leq"),
    Rewrite(ReAll(), ReStar(ReAllChar()), "regexp-all"),
    # Rewrite(ReOpt(a), ReUnion(StrToRe(""), a), "regexp-opt"),
    Rewrite(ReDiff(a, b), ReIntersect(a, ReComp(b)), "regexp-diff"),
    # Rewrite(ReConcat(a, StrToRe(""), b), ReConcat(a, b), "regexp-concat-empty"),
    # Rewrite(ReConcat(a, ReNone(), b), ReNone(), "regexp-concat-none"),
    # Rewrite(ReConcat(a, ReConcat(b, c), d), ReConcat(a, b, c, d), "regexp-concat-assoc"),
    # Rewrite(ReConcat(a, ReStar(b), b, c), ReConcat(a, b, ReStar(b), c), "regexp-concat-star"),
    # Rewrite(ReConcat(a, ReStar(b), ReStar(b), c), ReConcat(a, ReStar(b), c), "regexp-concat-star"),
    # Rewrite(ReConcat(a, StrToRe(b), StrToRe(c), d), ReConcat(a, StrToRe(Concat(b, c)), d), "regexp-concat-strings"),
    Rewrite(ReUnion(a, ReStar(ReAllChar())), ReStar(ReAllChar()), "regexp-union-allchar"),
    Rewrite(ReUnion(ReUnion(a, ReNone()), b), ReUnion(a, b), "regexp-union-none"),
    # Rewrite(ReUnion(a, ReUnion(b, c), d), ReUnion(a, b, c, d), "regexp-union-assoc"),
    Rewrite(ReUnion(ReUnion(a, b), b), ReUnion(a, b), "regexp-union-idemp"),
    Rewrite(ReIntersect(ReIntersect(a, ReStar(ReAllChar())), b), ReIntersect(a, b), "regexp-inter-allchar"),
    Rewrite(ReIntersect(ReIntersect(a, ReNone()), b), ReNone(), "regexp-inter-none"),
    # Rewrite(ReIntersect(a, ReIntersect(b, c), d), ReIntersect(a, b, c, d), "regexp-inter-assoc"),
    # Rewrite(ReIntersect(a, b, c, b, d), ReIntersect(a, b, c, d), "regexp-inter-idemp"),
    # Rewrite(ReStar(ReNone()), StrToRe(""), "regexp-star-none"),
    # Rewrite(RegExpLoop(a, b, c), ReNone(), "regexp-loop-none"),
    # Rewrite(ReIntersect(a, StrToRe(b), c), StrToRe(b), "regexp-inter-single"),
    # Rewrite(ReIntersect(a, StrToRe(b), c), ReNone(), "regexp-inter-false"),
    Rewrite(StrSubstr(Concat(a, b), c, d), StrSubstr(a, c, d), "substr-of-concat2"),
    Rewrite(StrSubstr(Concat(Concat(a, b), c), 0, d), Concat(a, StrSubstr(Concat(b, c), 0, Sub(d, StrLen(a)))), "substr-zero-start2"),
    Rewrite(StrSubstr(Concat(Concat(a, b), c), d, e), StrSubstr(Concat(b, c), Sub(d, StrLen(a)), e), "substr-of-concat1"),
    # Rewrite(StrLen(StringRev(a)), StrLen(a), "length-of-reverse"),
    # Rewrite(StringRev(StringRev(a)), a, "reverse-of-reverse"),
    # Rewrite(StringRev(Concat(Concat(a, b), c)), StringRev(Concat(a, b)), "reverse-of-concat"),
    # Rewrite(StrLen(SeqUnit(a)), 1, "length-of-sequnit"),
    # Rewrite(SeqNth(SeqUnit(a), 0), a, "seqnth-sequnit"),
    # Rewrite(StringRev(SeqUnit(a)), SeqUnit(a), "reverse-of-sequnit"),
    ]

STRING_ADDITIONAL_RULES = [
    Rewrite(StrReplace(a, a, b), b, "replace-x-x-y-to-y"),
    Rewrite(StrReplace(a, b, b), a, "replace-x-y-y-to-x"),
    Rewrite(StrReplace(a, EmptyString(), b), Concat(b, a), "replace-x-empty-y-to-concat-y-x"),
    Rewrite(Concat(b, a), StrReplace(a, EmptyString(), b), "replace-x-empty-y-to-concat-y-x-reverse"),
    Rewrite(StrIndexof(a, a, c), StrIndexof(EmptyString(), EmptyString(), c), "indexof-x-x-i-to-indexof-empty-empty-i"),
    Rewrite(StrIndexof(a, b, Neg(1)), Neg(1), "indexof-x-y-neg1-to-neg1"),
    Rewrite(StrSubstr(a, b, 0), EmptyString(), "substr-x-y-0-to-empty"),
    Rewrite(StrSubstr(a, Neg(1), b), EmptyString(), "substr-x-neg1-y-to-empty"),
    Rewrite(StrSubstr(a, b, Neg(1)), EmptyString(), "substr-x-y-neg1-to-empty"),
    Rewrite(StrAt(EmptyString(), a), EmptyString(), "str-at-empty-x-to-empty"),
    Rewrite(StrReplace(EmptyString(), a, EmptyString()), EmptyString(), "replace-empty-x-empty-to-empty"),
    Rewrite(StrSubstr(EmptyString(), a, a), EmptyString(), "substr-empty-x-x-to-empty"),
    Rewrite(StrIndexof(EmptyString(), a, 1), Neg(1), "indexof-empty-x-1-to-neg1"),
    Rewrite(StrSubstr(EmptyString(), 1, a), EmptyString(), "substr-empty-1-x-to-empty"),
    Rewrite(StrSubstr(EmptyString(), 0, a), EmptyString(), "substr-empty-0-x-to-empty"),
    Rewrite(StrIndexof(a, EmptyString(), 0), 0, "indexof-x-empty-0-to-0"),
    ]


BV_RULES = [
    # Rewrite(BvConcat(a, BvConcat(b, c), d), BvConcat(a, b, c, d), "concat-assoc"),
    # Rewrite(BvConcat(a, Extract(k1, j1, b), Extract(j2, i1, b), c), BvConcat(a, Extract(k1, i1, b), c), "concat-extract-merge"),
    # Rewrite(Extract(a, b, c), BvConcat(Extract(a, Add(d, 1), c), Extract(d, b, c)), "concat-extract-merge"),
    Rewrite(BvConcat(Extract(a, Add(d, 1), c), Extract(d, b, c)), Extract(a, b, c), "concat-extract-split"),
    # Rewrite(Extract(l1, k2, Extract(j3, i2, a)), Extract(m1, n1, a), "extract-extract"),
    # Rewrite(Extract(n2, 0, a), a, "extract-all"),
    # Rewrite(Extract(j4, i3, BvConcat(BvConcat(a, b), c)), Extract(j4, i3, c), "extract-concat-last"),
    # Rewrite(Extract(j5, i4, BvConcat(BvConcat(a, b), c)), BvConcat(Extract(u1, 0, BvConcat(a, b)), Extract(u2, i4, c)), "extract-concat-split"),
    # Rewrite(Extract(j6, i5, BvConcat(BvConcat(a, b), c)), Extract(u3, l2, BvConcat(a, b)), "extract-concat-prefix"),
    # Rewrite(Extract(j7, i6, BvConcat(BvConcat(a, b), c)), Extract(j7, i6, BvConcat(b, c)), "extract-concat-drop-first"),
    # Rewrite(Extract(j8, i7, BvAnd(a, b)), BvAnd(Extract(j8, i7, a), Extract(j8, i7, b)), "extract-bvand"),
    # Rewrite(Extract(j9, i8, BvOr(a, b)), BvOr(Extract(j9, i8, a), Extract(j9, i8, b)), "extract-bvor"),
    # Rewrite(Extract(j10, i9, BvXor(a, b)), BvXor(Extract(j10, i9, a), Extract(j10, i9, b)), "extract-bvxor"),
    # Rewrite(Extract(j11, i10, BvNot(a)), BvNot(Extract(j11, i10, a)), "extract-bvnot"),
    # Rewrite(Extract(high1, low1, SignExtend(k3, a)), Extract(high1, low1, a), "extract-sign-extend-elim"),
    # Rewrite(Extract(high2, low2, SignExtend(k4, a)), SignExtend(s1, Extract(n3, low2, a)), "extract-sign-extend"),
    # Rewrite(Extract(high3, low3, SignExtend(k5, a)), Repeat(r1, Extract(n4, n4, a)), "extract-sign-extend-repeat"),
    # Rewrite(BvNeg(BvMul(a, BvConst(n5, m1), b)), BvMul(a, BvConst(Neg(n5), m1), b), "bvneg-bvmul-const-neg"),
    # Rewrite(BvNeg(BvAdd(a, b, c)), BvNeg(BvAdd(b, c)), "bvneg-bvadd-skip-first"),
    # Rewrite(BvMul(BvNeg(a), BvConst(n6, m2)), BvMul(a, BvConst(Neg(n6), m2)), "bvmul-bvneg-const"),
    # Rewrite(BvMul(BvAdd(a, b), BvConst(n7, m3)), BvAdd(BvMul(a, BvConst(n7, m3)), BvMul(b, BvConst(n7, m3))), "bvmul-distribute-add"),
    # Rewrite(BvMul(BvSub(a, b), BvConst(n8, m4)), BvSub(BvMul(a, BvConst(n8, m4)), BvMul(b, BvConst(n8, m4))), "bvmul-distribute-sub"),
    Rewrite(BvMul(BvAdd(a, b), c), BvAdd(BvMul(a, c), BvMul(b, c)), "bvmul-add-distrib"),
    Rewrite(BvMul(c, BvAdd(a, b)), BvAdd(BvMul(c, a), BvMul(c, b)), "bvmul-comm-add-distrib"),
    Rewrite(BvNot(BvXor(a, b)), BvXor(BvNot(a), b), "bvnot-bvxor"),
    # Rewrite(BvAnd(a, c, b, c, d), BvAnd(a, c, b, d), "bvand-idempotent"),
    # Rewrite(BvAnd(a, c, b, BvNot(c), d), BvConst(0, w1), "bvand-complement-zero"),
    # Rewrite(BvOr(a, c, b, c, d), BvOr(a, c, b, d), "bvor-idempotent"),
    # Rewrite(BvOr(a, c, b, BvNot(c), d), BvNot(BvConst(0, w2)), "bvor-complement-all-ones"),
    # Rewrite(BvXor(a, c, b, c, d), BvXor(a, b, d), "bvxor-idempotent"),
    # Rewrite(BvXor(a, c, b, BvNot(c), d), BvNot(BvXor(a, b, d)), "bvxor-complement"),
    # Rewrite(BvXor(a, BvNot(c), b, c, d), BvNot(BvXor(a, b, d)), "bvxor-complement-swap"),
    # Rewrite(BvUlt(a, BvAdd(b, c1)), And(Not(Eq(b, BvNot(BvConst(0, w3)))), Not(BvUlt(b, a))), "bvult-bvadd"),
    # Rewrite(BvConcat(Extract(i1, n0, a), BvConst(n0, m5)), BvMul(a, BvShl(BvConst(1, w4), BvConst(m5, w4))), "concat-extract-const"),
    # Rewrite(BvSlt(BvMul(SignExtend(n9, BvAdd(a, t1)), SignExtend(m6, b)), BvMul(SignExtend(n9, a), SignExtend(m6, b))), And(Not(Eq(t1, BvConst(0, tn1))), Not(Eq(b, BvConst(0, an1))), Eq(BvSlt(BvAdd(a, t1), a), BvSgt(b, BvConst(0, an1)))), "bvslt-bvmul"),
    # Rewrite(BvSlt(BvMul(ZeroExtend(n10, BvAdd(a, t2)), SignExtend(m7, b)), BvMul(ZeroExtend(n10, a), SignExtend(m7, b))), And(Not(Eq(t2, BvConst(0, tn2))), Not(Eq(b, BvConst(0, an2))), Eq(BvUlt(BvAdd(a, t2), a), BvSgt(b, BvConst(0, an2)))), "bvslt-zero-ext"),
    Rewrite(BvAnd(a, b), BvAnd(b, a), "bvand-comm"),
    Rewrite(BvOr(a, b), BvOr(b, a), "bvor-comm"),
    Rewrite(BvXor(a, b), BvXor(b, a), "bvxor-comm"),
    Rewrite(BvMul(a, b), BvMul(b, a), "bvmul-comm"),
    # Rewrite(BvOr(a, BvConst(0, n11)), a, "bvor-zero"),
    # Rewrite(BvMul(a, BvConst(1, w5)), a, "bvmul-one"),
    # Rewrite(BvMul(a, BvConst(0, w6)), BvConst(0, w6), "bvmul-zero"),
    # Rewrite(BvAdd(a, BvConst(0, w7)), a, "bvadd-zero"),
    # Rewrite(BvAdd(a, a), BvMul(a, BvConst(2, w8)), "bvadd-double"),
    # Rewrite(ZeroExtend(0, a), a, "zero-extend-zero"),
    # Rewrite(SignExtend(0, a), a, "sign-extend-zero"),
    Rewrite(Eq(a, BvNot(a)), FALSE(), "eq-bvnot-false"),
    # Rewrite(BvUlt(a, BvConst(n12, w9)), Distinct(a, BvConst(n12, w9)), "bvult-distinct"),
    # Rewrite(BvOr(a, BvOr(b, c), d), BvOr(a, b, c, d), "bvor-assoc"),
    # Rewrite(BvXor(a, BvXor(b, c), d), BvXor(a, b, c, d), "bvxor-assoc"),
    # Rewrite(BvAnd(a, BvAnd(b, c), d), BvAnd(a, b, c, d), "bvand-assoc"),
    # Rewrite(BvMul(a, BvMul(b, c), d), BvMul(a, b, c, d), "bvmul-assoc"),
    # Rewrite(BvConcat(a, BvConst(n13, w10), BvConst(n14, w11), d), BvConcat(a, BvConst(Add(Mult(n13, Pow2(w11)), n14), w12), d), "concat-const-merge"),
    Rewrite(BvAdd(a, b), BvAdd(b, a), "bvadd-comm"),
    Rewrite(BvNeg(BvSub(a, b)), BvSub(b, a), "bvneg-bvsub"),
    # Rewrite(BvNeg(BvNeg(a)), a, "bvneg-neg"),
    Rewrite(BvSub(a, b), BvAdd(a, BvNeg(b)), "bvsub-to-bvadd-neg"),
    ]




# ALL_RULES = ARITH_RULES + CORE_RULES + STRING_RULES + STRING_ADDITIONAL_RULES + ARITH_ADDITIONAL_RULES + BV_RULES
# ALL_RULES = ARITH_RULES + CORE_RULES + STRING_RULES + STRING_ADDITIONAL_RULES + ARITH_ADDITIONAL_RULES

ALL_RULES = STRING_ADDITIONAL_RULES + ARITH_ADDITIONAL_RULES



def RewriteEGG(expr: Expr, rule_set: list, orig_sexpr: list, sample_size: int = 1, attempts: int = 10) -> list:
    """
    Rewrite expressions using equality saturation with EGraph.
    
    Args:
        expr: The expression to rewrite
        rule_set: List of rewrite rules to apply
        orig_sexpr: Original s-expressions for similarity checking
        sample_size: Number of samples to generate
        attempts: Maximum attempts per sample
        
    Returns:
        List of rewritten expressions or None if failed
    """
    @exit_after(30)
    def RewriteExpr(expr: Expr, rule_set: list, orig_sexpr: set, sample_size: int = 1, attempts: int = 10) -> list:
        random_exprs = []
        egraph = EGraph()
        root = egraph.add(expr)
        
        # Run rewrite rules
        # print(f"Running EGraph with {len(rule_set)} rules...")
        egraph.run(rule_set)

        # print("EGraph run completed. Extracting random expressions...")
        
        # Convert orig_sexpr to set once if not already
        orig_sexpr_set = orig_sexpr if isinstance(orig_sexpr, set) else set(orig_sexpr)
        
        max_distinct_score = 0
        best_expr = None
        
        for i in range(sample_size):
            # print(f"Attempting to extract expression {i + 1}/{sample_size}...")
            for diversity_attempt in range(attempts):
                try:
                    # print(f"Trying to extract a random expression (attempt {diversity_attempt + 1}/{attempts})...")
                    random_expr = egraph.random_extract(root, 30, 30)

                    # print("Extracted random expression, converting to string...")
                    random_expr_str = convert_IR_to_str(random_expr)
                    
                    # print(f"Converted completed, parsing expression ...")
                    # Parse and validate the expression
                    temp_script, _ = parse_str(f"(assert {random_expr_str})")
                    if not isinstance(temp_script, Script):
                        continue
                        
                    temp_term = temp_script.assert_cmd[0].term
                    if not isinstance(temp_term, Term):
                        continue
                    
                    # Extract subterms more efficiently
                    sexprs = {str(term) for term in temp_term.get_all_subterms()}
                    
                    distinct_score = check_similarity(sexprs, orig_sexpr_set)

                    # print("Checked similarity")
                    
                    # Update best expression if this one is better
                    if distinct_score > max_distinct_score:
                        max_distinct_score = distinct_score
                        best_expr = random_expr
                    
                    # Accept expression based on similarity score
                    if random.uniform(0, 1) < distinct_score:
                        # print(f"Accepted expression with score {distinct_score:.4f}: {random_expr_str}")
                        random_exprs.append(random_expr)
                        break

                    # print(f"Rejected expression with score {distinct_score:.4f}: {random_expr_str}")
                        
                except Exception as e:
                    # Skip invalid expressions silently but could log for debugging
                    # print(f"Exception during extraction: {e}")
                    continue
            else:
                # If no expression was accepted in all attempts, use the best one found
                if best_expr is not None:
                    random_exprs.append(best_expr)
        
        # If no expressions were found, return the original expression
        if not random_exprs:
            random_exprs.append(expr)
        
        return random_exprs
    
    try:
        # Convert orig_sexpr to set for better performance
        orig_sexpr_set = set(orig_sexpr) if not isinstance(orig_sexpr, set) else orig_sexpr
        result = RewriteExpr(expr, rule_set, orig_sexpr_set, sample_size, attempts)
        return result if result else [expr]  # Return original if empty
    except KeyboardInterrupt:
        print("Rewriting timeout")
        return [expr]  # Return original expression on timeout
    except Exception as e:
        print(f"Error during rewriting: {e}")
        return [expr]  # Return original expression on error
    

def check_similarity(sexprs1: set, sexprs2: set) -> float:
    """
    Calculate similarity score between two sets of s-expressions.
    
    Args:
        sexprs1: First set of s-expressions
        sexprs2: Second set of s-expressions
        
    Returns:
        Similarity score as a float between 0 and 1
    """
    if not sexprs1:  # Handle empty set case
        return 0.0
    
    distinct_count = len(sexprs1 - sexprs2)
    total_count = len(sexprs1)
    return distinct_count / total_count


if __name__ == "__main__":
    a, b, c, d, e, f = vars("a b c d e f")
    # s, g = parse_file("../../test/case8.smt2")
    # s, g = parse_str("(declare-fun fdjisoiefm23 () Int) (assert (= fdjisoiefm23 (* 0 fdjisoiefm23)))")
    s, g = parse_str("(declare-fun x () String) (assert (= true (str.contains x x)))")
    # for op_occ in s.op_occs:
    #     print(op_occ)
    random_term = random.choice(s.op_occs)
    subterms = random_term.get_all_subterms()
    sexprs = []
    for term in subterms:
        sexprs.append(str(term))
    ir = convert_to_IR(random_term)
    print(convert_IR_to_str(ir))
    
    # Fix: Handle empty result from RewriteEGG
    transformed_irs = RewriteEGG(ir, ALL_RULES, sexprs)
    if transformed_irs:
        transformed_ir = transformed_irs[0]
        print(convert_IR_to_str(transformed_ir))
        new_term_str = convert_IR_to_str(transformed_ir)
        if "any_int" in new_term_str:
            # generate a random term
            def_candidate, term_candidate = GENERATORS["int"]()
            print(f"Generated term: {term_candidate}")
            print(f"Generated definition: {def_candidate}")
            new_term_str = new_term_str.replace("any_int", term_candidate)
        print(f"Transformed term: {new_term_str}")
    else:
        print("No transformations found or rewriting failed")
        print("Original expression will be used")


"""
    # Rewrite(Mul(Add(1, 'x'), Sub(1, 'x')), rules)
    # Parse a file
    s, g = parse_file("../../test/case8.smt2")
    # for op_occ in s.op_occs:
    #     print(op_occ)
    random_term = random.choice(s.op_occs)
    subterms = random_term.get_all_subterms()
    sexprs = []
    for term in subterms:
        sexprs.append(str(term))
    ir = convert_to_IR(random_term)
    print(convert_IR_to_str(ir))
    transformed_ir = Rewrite(ir, ALL_RULES, sexprs)[0]
    print(convert_IR_to_str(transformed_ir))
    # print(random_term)
    # print(random_term.parent)
    # for ast_cmd in s.assert_cmd:
    #     ir = convert_to_IR(ast_cmd.term)
    #     print(convert_IR_to_str(ir))
    #     transformed_ir = Rewrite(ir, ALL_RULES)
    #     print(convert_IR_to_str(transformed_ir))
"""