import sys

sys.path.append("..")

from src.parsing.Ast import Term
from src.parsing.Parse import parse_file
from src.parsing.Types import (
    NOT, AND, IMPLIES, OR, XOR, IFF
)


def process_seed(seed):
    script, glob = parse_file(seed, silent=True)
    return script, glob


def get_subterms(expr):
    """
    Get all subexpression of term object expr.
    :returns: av_expr list of expressions
              expr_types list of types
              (s.t. expression e = av_expr[i] has type expr_types[i])
    """
    av_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = get_subterms(s)
                av_expr += new_av
                expr_types += new_type
            new_type = expr.type
            expr_types.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_types.append(expr.type)
    elif type(expr) != str:
        if expr.term:
            new_av, new_type = get_subterms(expr.term)
            av_expr += new_av
            expr_types += new_type
    return av_expr, expr_types


def get_basic_subterms(expr, index, rename_flag=False):
    """
    Get all basic subexpression of term object expr.
    :param expr: a term object representing an SMT formula
    :param index: an integer representing the number of the assert containing the expression
    :param rename_flag: a boolean flag indicating whether to rename quantified variables
    :return: a list of term objects representing basic subexpressions of the input formula, 
    and a list of types representing the types of the corresponding basic subexpressions
    """
    basic_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.op in [NOT, AND, IMPLIES, OR, XOR, IFF] or expr.quantifier is not None or expr.let_terms is not None:
            if expr.quantifier is not None and rename_flag:
                # Rename quantified variables if rename_flag is True
                for v in range(len(expr.quantified_vars[0])):
                    expr.quantified_vars[0][v] = 'VAR' + str(v)
                for t in range(len(expr.quantified_vars[1])):
                    expr.quantified_vars[1][t] = 'TYPE' + str(t)
            # Recursively get basic subexpressions for the subterms of expr
            for s in expr.subterms:
                new_av, new_type = get_basic_subterms(s, index, rename_flag)
                basic_expr += new_av
                expr_types += new_type
        else:
            # This is a basic subexpression, so add it to the list
            basic_expr.append([expr, index])
            expr_types.append(expr.type)
    elif isinstance(expr, str):
        pass
        # This is not a term object, so do nothing
    else:
        # This is a let-binding expression, so get basic subexpressions for its term
        if expr.term:
            new_av, new_type = get_basic_subterms(expr.term, index, rename_flag)
            basic_expr += new_av
            expr_types += new_type
    return basic_expr, expr_types


def get_all_basic_subformula(formula, rename_flag=False):
    """
    Get all basic subformulas (those that don't contain any logical connectives).
    :param formula: parsed SMT script
    :param rename_flag: whether to rename quantified variables
    :return: a list of basic subformulas
    """
    basic_expr = list()
    for i in range(len(formula.assert_cmd)):
        exps, typ = get_basic_subterms(formula.assert_cmd[i], i, rename_flag)
        basic_expr += exps
    return basic_expr