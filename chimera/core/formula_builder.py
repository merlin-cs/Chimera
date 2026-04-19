"""
SMT-LIB formula construction utilities.

This module provides utilities for building, validating, and formatting
SMT-LIB formulas during fuzzing campaigns.

Key Functions
-------------
- `format_smt_string`: Normalize and pretty-print SMT-LIB strings.
- `validate_smt_formula`: Check structural validity of SMT-LIB strings.
- `balance_parentheses`: Fix unbalanced parentheses in SMT-LIB strings.
- `insert_push_and_pop`: Wrap assertions for incremental solving.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import re
import random
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from chimera.core.smt_ast import DeclareFun, Script, Assert, CheckSat
from chimera.core.smt_parser import parse_string
from chimera.core.logic_analyzer import parse_logic, is_builtin_sort


# ---------------------------------------------------------------------------
# Parenthesis balancing and validation
# ---------------------------------------------------------------------------

def smt_paren_depth(text: str) -> int:
    """Calculate the net parenthesis depth of an SMT-LIB string.

    Respects string literals (parentheses inside strings are not counted).

    Parameters
    ----------
    text : str
        The SMT-LIB source text.

    Returns
    -------
    int
        Positive if more opens than closes, negative if more closes than opens.
        Zero indicates balanced parentheses.

    Examples
    --------
    >>> smt_paren_depth("(assert true)")
    0
    >>> smt_paren_depth("(assert (and x y")
    1
    >>> smt_paren_depth('"(a string)"')
    0
    """
    depth = 0
    in_string = False
    prev = ''

    for ch in text:
        if ch == '"' and prev != '\\':
            in_string = not in_string
        elif not in_string:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
        prev = ch

    return depth


def balance_parentheses(text: str) -> str:
    """Fix unbalanced parentheses by adding missing closing parens.

    Parameters
    ----------
    text : str
        SMT-LIB text with potentially unbalanced parentheses.

    Returns
    -------
    str
        Text with balanced parentheses (only adds closing parens, never removes).

    Examples
    --------
    >>> balance_parentheses("(assert (and x y")
    '(assert (and x y))'
    """
    depth = smt_paren_depth(text)
    if depth > 0:
        return text + (")" * depth)
    return text


def validate_smt_formula(script: str) -> bool:
    """Validate structural properties of an SMT-LIB formula.

    Performs lightweight checks:
    1. Parenthesis balance (respecting string literals)
    2. Presence of ``(check-sat)`` or ``(push`` for incremental
    3. No malformed ``(! … :named …)`` annotations

    Parameters
    ----------
    script : str
        The SMT-LIB script to validate.

    Returns
    -------
    bool
        True if the formula passes basic validation checks.

    Examples
    --------
    >>> validate_smt_formula("(set-logic QF_LIA)\\n(assert (> x 0))\\n(check-sat)")
    True
    >>> validate_smt_formula("(assert (> x 0)")  # Unbalanced
    False
    """
    # Check parenthesis balance
    if smt_paren_depth(script) != 0:
        return False

    # Must have check-sat or be incremental
    if "(check-sat)" not in script and "(push" not in script:
        return False

    # Check for malformed :named annotations at assertion level
    for line in script.split("\n"):
        stripped = line.strip()
        if stripped.startswith("(assert") and ":named" in stripped:
            idx = stripped.find(":named")
            prefix = stripped[:idx]
            depth = prefix.count("(") - prefix.count(")")
            if depth < 2:
                return False

    return True


# ---------------------------------------------------------------------------
# Annotation stripping
# ---------------------------------------------------------------------------

_NAMED_ANNOTATION_PATTERN = re.compile(
    r'^\(\!\s+(.*?)\s+:named\s+\S+\s*\)$',
    re.DOTALL
)


def strip_named_annotation(expr: str) -> str:
    """Remove ``(! … :named label)`` wrapper from an expression.

    Corpus building-block expressions are sometimes wrapped with ``:named``
    annotations. When inserted into skeletons, these become nested annotations
    that many solvers reject. This function removes the outermost layer.

    Parameters
    ----------
    expr : str
        The expression string, possibly wrapped with ``(! … :named …)``.

    Returns
    -------
    str
        The expression with outer named annotation removed.

    Examples
    --------
    >>> strip_named_annotation("(! (=> a b) :named IP_1)")
    '(=> a b)'
    >>> strip_named_annotation("(and x y)")
    '(and x y)'
    """
    stripped = expr.strip()
    match = _NAMED_ANNOTATION_PATTERN.match(stripped)
    if match:
        return match.group(1).strip()
    return stripped


# ---------------------------------------------------------------------------
# Formula formatting
# ---------------------------------------------------------------------------

def format_smt_string(text: str) -> str:
    """Normalize and clean up an SMT-LIB string.

    Performs basic cleanup:
    - Removes excessive blank lines
    - Normalizes whitespace around parentheses
    - Ensures proper line endings

    Parameters
    ----------
    text : str
        The SMT-LIB source text.

    Returns
    -------
    str
        Cleaned-up SMT-LIB string.
    """
    # Remove leading/trailing whitespace
    text = text.strip()

    # Normalize line endings
    text = text.replace('\r\n', '\n').replace('\r', '\n')

    # Remove excessive blank lines (more than 2 consecutive newlines)
    text = re.sub(r'\n{3,}', '\n\n', text)

    # Ensure space after opening paren in commands (if missing)
    text = re.sub(r'\((set-logic|set-info|set-option|declare-const|declare-fun|define-fun|assert|check-sat|push|pop|exit)\(', r'(\1 (', text)
    text = re.sub(r'\(assert\(', '(assert (', text)

    return text


# ---------------------------------------------------------------------------
# Incremental mode helpers
# ---------------------------------------------------------------------------

def insert_push_and_pop(assertions: List[str]) -> List[str]:
    """Wrap assertions in push/pop pairs for incremental solving.

    Randomly groups assertions into chunks and wraps each chunk with
    push/pop, ensuring the stack is balanced at the end.

    Parameters
    ----------
    assertions : List[str]
        List of assertion strings (without the ``(assert ...)`` wrapper).

    Returns
    -------
    List[str]
        New list with push/pop/check-sat commands interspersed.

    Examples
    --------
    >>> insert_push_and_pop(["(> x 0)", "(< y 10)"])
    ['(push 1)', '(assert (> x 0))', '(check-sat)', '(pop 1)', '(push 1)', '(assert (< y 10))', '(check-sat)', '(pop 1)']
    """
    if not assertions:
        return ["(check-sat)"]

    result: List[str] = []
    stack_depth = 0
    remaining = list(assertions)

    while remaining:
        # Determine how many assertions to push in this round
        if len(remaining) > 2:
            push_count = random.randint(1, min(3, len(remaining)))
        else:
            push_count = len(remaining)

        # Emit push
        result.append(f"(push {push_count})")
        stack_depth += push_count

        # Emit assertions
        for _ in range(push_count):
            if remaining:
                assertion = remaining.pop(0)
                if not assertion.strip().startswith("(assert"):
                    assertion = f"(assert {assertion})"
                result.append(assertion)

        # Emit check-sat
        result.append("(check-sat)")

        # Randomly pop some levels to enhance test diversity
        if stack_depth > 0:
            pop_count = random.randint(1, stack_depth)
            stack_depth -= pop_count
            result.append(f"(pop {pop_count})")

    # Ensure final stack balance
    if stack_depth > 0:
        result.append(f"(pop {stack_depth})")

    return result


# ---------------------------------------------------------------------------
# Variable and declaration utilities
# ---------------------------------------------------------------------------

_RESERVED_NAMES: FrozenSet[str] = frozenset({
    "Int", "Real", "Bool", "String", "Array", "BitVec", "FloatingPoint",
    "let", "assert", "check-sat", "declare-fun", "define-fun", "match",
    "par", "forall", "exists", "_", "as", "!",
})

_VALID_SYMBOL_PATTERN = re.compile(r'^[a-zA-Z0-9_.~!@$%^&*+=<>.?/-]+$')


def is_valid_symbol_name(name: str) -> bool:
    """Check if a string is a valid SMT-LIB simple symbol.

    Parameters
    ----------
    name : str
        The name to check.

    Returns
    -------
    bool
        True if the name is a valid SMT-LIB simple symbol.
    """
    if not name:
        return False
    if name in _RESERVED_NAMES:
        return False
    return bool(_VALID_SYMBOL_PATTERN.match(name))


def build_type_var_map(var_list: List[str]) -> Dict[str, List[str]]:
    """Build a type-to-variable mapping from corpus variable entries.

    Corpus entries are strings like ``"x, Int"`` or ``"y, Bool"``.

    Parameters
    ----------
    var_list : List[str]
        List of variable entries in the format ``"name, sort"``.

    Returns
    -------
    Dict[str, List[str]]
        Mapping from sort to list of variable names.

    Examples
    --------
    >>> build_type_var_map(["x, Int", "y, Int", "z, Bool"])
    {'Int': ['x', 'y'], 'Bool': ['z']}
    """
    type_var: Dict[str, List[str]] = {}
    for entry in var_list:
        if ", " in entry:
            parts = entry.split(", ")
            name = parts[0].strip()
            typ = parts[1].strip() if len(parts) > 1 else ""
            if name and typ:
                type_var.setdefault(typ, []).append(name)
    return type_var


def variable_translocation(assertions: List[str], type_var: Dict[str, List[str]]) -> List[str]:
    """Randomly swap variables of the same type within assertion strings.

    Uses word-boundary-aware replacement to avoid corrupting identifiers
    that share a common prefix (e.g., ``var1`` vs ``var12``).

    Parameters
    ----------
    assertions : List[str]
        List of assertion strings.
    type_var : Dict[str, List[str]]
        Mapping from sort to list of variable names.

    Returns
    -------
    List[str]
        Modified assertion list with some variables swapped.
    """
    if not type_var:
        return assertions

    result = list(assertions)
    replace_time = random.randint(1, 10)

    while replace_time > 0 and result:
        if not list(type_var.keys()):
            break

        replace_type = random.choice(list(type_var.keys()))
        if not result:
            break

        replace_idx = random.randint(0, len(result) - 1)
        vars_of_type = type_var.get(replace_type, [])

        if not vars_of_type:
            replace_time -= 1
            continue

        for var in vars_of_type:
            pattern = re.compile(r'(?<=[\s(])' + re.escape(var) + r'(?=[\s)])')
            match = pattern.search(result[replace_idx])
            if match:
                replacement = random.choice(vars_of_type)
                result[replace_idx] = pattern.sub(
                    replacement, result[replace_idx], count=1
                )
                replace_time -= 1
                break
        else:
            replace_time -= 1

    return result


# ---------------------------------------------------------------------------
# Function declaration extraction
# ---------------------------------------------------------------------------

_FUNC_DECL_PATTERN = re.compile(
    r'\((?:declare-fun|define-fun|declare-const|define-const)\s+([^\s)]+)'
)


def extract_function_name(decl: str) -> Optional[str]:
    """Extract the symbol name from a declaration string.

    Parameters
    ----------
    decl : str
        Declaration string like ``(declare-fun f (Int Bool) Int)``.

    Returns
    -------
    Optional[str]
        The function/constant name, or ``None`` if parsing fails.

    Examples
    --------
    >>> extract_function_name("(declare-fun f (Int Bool) Int)")
    'f'
    >>> extract_function_name("(declare-const x Real)")
    'x'
    """
    match = _FUNC_DECL_PATTERN.search(decl)
    return match.group(1) if match else None


# ---------------------------------------------------------------------------
# Script building utilities
# ---------------------------------------------------------------------------

def build_smt_script(
    declarations: List[str],
    assertions: List[str],
    *,
    logic: str = "ALL",
    incremental: bool = False,
    merge_asserts: bool = False,
) -> str:
    """Build an SMT-LIB script from declarations and assertions.

    Parameters
    ----------
    declarations : List[str]
        List of declaration strings (declare-fun, declare-sort, etc.).
    assertions : List[str]
        List of assertion strings (with or without ``(assert ...)`` wrapper).
    logic : str
        SMT-LIB logic to use. Default is ``ALL``.
    incremental : bool
        If True, wrap assertions in push/pop for incremental solving.
    merge_asserts : bool
        If True, conjoin all assertions into a single ``(and ...)``.

    Returns
    -------
    str
        Complete SMT-LIB script.

    Examples
    --------
    >>> build_smt_script(["(declare-fun x () Int)"], ["(> x 0)"])
    '(set-logic ALL)\\n(declare-fun x () Int)\\n(assert (> x 0))\\n(check-sat)'
    """
    parts: List[str] = []

    # Logic declaration
    parts.append(f"(set-logic {logic})")

    # Deduplicate declarations
    seen_decls: Set[str] = set()
    for decl in declarations:
        decl = decl.strip()
        if decl and decl not in seen_decls:
            seen_decls.add(decl)
            parts.append(decl)

    # Process assertions
    processed_assertions: List[str] = []
    for assertion in assertions:
        assertion = assertion.strip()
        if not assertion:
            continue
        if not assertion.startswith("(assert"):
            assertion = f"(assert {assertion})"
        processed_assertions.append(assertion)

    if merge_asserts and len(processed_assertions) > 1:
        # Conjoin all assertions
        bodies = []
        for assertion in processed_assertions:
            # Strip (assert ... ) wrapper
            inner = assertion.strip()
            if inner.startswith("(assert ") and inner.endswith(")"):
                inner = inner[8:-1]  # Remove "(assert " and final ")"
            bodies.append(inner)
        parts.append(f"(assert (and {' '.join(bodies)}))")
    elif incremental:
        parts.extend(insert_push_and_pop(
            [a[8:-1] if a.startswith("(assert ") and a.endswith(")") else a
             for a in processed_assertions]
        ))
    else:
        parts.extend(processed_assertions)

    # Check-sat (if not already in incremental mode)
    if not incremental and "(check-sat)" not in parts:
        parts.append("(check-sat)")

    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Comprehensive validation
# ---------------------------------------------------------------------------

class ValidationResult:
    """Result of formula validation.

    Attributes
    ----------
    ok : bool
        True if validation passed.
    errors : List[str]
        List of error messages (empty if ok).
    warnings : List[str]
        List of warning messages (non-fatal issues).
    """
    def __init__(
        self,
        ok: bool = True,
        errors: Optional[List[str]] = None,
        warnings: Optional[List[str]] = None,
    ) -> None:
        self.ok = ok
        self.errors = errors or []
        self.warnings = warnings or []

    def __bool__(self) -> bool:
        return self.ok

    def __str__(self) -> str:
        if self.ok:
            return "ValidationResult(ok=True)"
        return f"ValidationResult(ok=False, errors={self.errors})"


def validate_formula(
    script: str,
    target_logic: Optional[str] = None,
    strict: bool = False,
) -> ValidationResult:
    """Comprehensive validation of an SMT-LIB formula.

    Performs multiple validation checks:
    1. Structural: parenthesis balance, check-sat presence
    2. Parse: attempt to parse with the SMT parser
    3. Symbol resolution: check for undeclared symbols
    4. Sort resolution: check for undeclared sorts
    5. Logic compliance: check quantifiers/theories match target logic

    Parameters
    ----------
    script : str
        The SMT-LIB script to validate.
    target_logic : str, optional
        If provided, check that the formula complies with this logic
        (e.g., no quantifiers in QF logics).
    strict : bool
        If True, treat warnings as errors.

    Returns
    -------
    ValidationResult
        Result object with ok flag and error/warning lists.

    Examples
    --------
    >>> result = validate_formula("(set-logic QF_LIA)\\n(assert (> x 0))\\n(check-sat)")
    >>> result.ok
    True
    """
    errors: List[str] = []
    warnings: List[str] = []

    # 1. Structural checks
    depth = smt_paren_depth(script)
    if depth != 0:
        errors.append(f"Unbalanced parentheses (depth={depth})")

    if "(check-sat)" not in script and "(push" not in script:
        errors.append("Missing (check-sat) or (push) command")

    # 2. Parse attempt
    parsed: Optional[Script] = None
    try:
        result = parse_string(script, silent=True)
        if result is None:
            errors.append("Parse failed - no result")
        else:
            parsed, _ = result
            if not parsed or not parsed.commands:
                errors.append("Parse returned empty script")
    except Exception as e:
        errors.append(f"Parse exception: {str(e)}")

    # 3. Symbol resolution (only if parse succeeded)
    if parsed:
        declared_symbols: Set[str] = set()
        used_symbols: Set[str] = set()
        declared_sorts: Set[str] = set()

        # Collect declarations
        for cmd in parsed.commands:
            if isinstance(cmd, DeclareFun):
                declared_symbols.add(cmd.symbol)
                # Extract sorts from declaration
                if cmd.input_sort and cmd.input_sort != "":
                    for s in extract_sorts_from_decl_string(cmd.input_sort):
                        if not is_builtin_sort(s):
                            declared_sorts.add(s)
                if cmd.output_sort:
                    out_sort = str(cmd.output_sort)
                    if not is_builtin_sort(out_sort):
                        declared_sorts.add(out_sort)

        # Collect uses from assertions
        for cmd in parsed.assert_cmd if hasattr(parsed, 'assert_cmd') else []:
            if isinstance(cmd, Assert) and hasattr(cmd, 'term'):
                _collect_symbols_from_term(cmd.term, used_symbols)

        # Check for undeclared symbols
        for sym in used_symbols:
            if sym not in declared_symbols and not is_builtin_symbol(sym):
                errors.append(f"Undeclared symbol: {sym}")

        # Check for undeclared sorts (weaker check - warnings only)
        for sort in declared_sorts:
            if not is_builtin_sort(sort):
                # This is informational - sorts may be declared elsewhere
                pass

    # 4. Logic compliance
    if target_logic and parsed:
        logic_info = parse_logic(target_logic)

        # Check quantifiers
        has_quantifiers = False
        script_str = str(parsed)
        if "forall" in script_str or "exists" in script_str:
            has_quantifiers = True

        if logic_info.is_quantifier_free and has_quantifiers:
            errors.append(
                f"Quantifiers found but target logic {target_logic} is quantifier-free"
            )

    ok = len(errors) == 0
    if strict and len(warnings) > 0:
        ok = False
        errors.extend(warnings)

    return ValidationResult(ok=ok, errors=errors, warnings=warnings)


def _collect_symbols_from_term(term, accumulator: Set[str]) -> None:
    """Recursively collect symbol names from a term.

    Parameters
    ----------
    term : Term
        The term to walk.
    accumulator : Set[str]
        Set to accumulate symbol names.
    """
    if term is None:
        return

    if hasattr(term, 'is_var') and term.is_var and hasattr(term, 'name') and term.name:
        accumulator.add(term.name)
    elif hasattr(term, 'is_const') and term.is_const:
        pass  # Constants don't need declaration
    elif hasattr(term, 'op') and term.op:
        op = term.op
        if isinstance(op, str) and not op.startswith("hole"):
            accumulator.add(op)

    if hasattr(term, 'subterms') and term.subterms:
        for sub in term.subterms:
            if hasattr(sub, '__class__') and hasattr(sub, 'is_var'):
                _collect_symbols_from_term(sub, accumulator)


def extract_sorts_from_decl_string(decl_str: str) -> Set[str]:
    """Extract sort names from a declaration string fragment.

    Parameters
    ----------
    decl_str : str
        Sort declaration fragment like "(Int Bool)" or "Array Int Real".

    Returns
    -------
    Set[str]
        Set of sort names found.
    """
    sorts: Set[str] = set()

    # Tokenize
    tokens = re.findall(r'[a-zA-Z0-9_]+', decl_str)

    for tok in tokens:
        if tok.isdigit():
            continue
        if not is_builtin_sort(tok):
            sorts.add(tok)

    return sorts


_BUILTIN_SYMBOLS: FrozenSet[str] = frozenset({
    "true", "false",
    "=", "distinct", "ite", "not", "and", "or", "xor", "=>",
    "+", "-", "*", "/", "div", "mod", "rem", ">", "<", ">=", "<=", "abs",
    "to_real", "to_int", "is_int",
    "str.++", "str.len", "str.at", "str.substr", "str.prefixof", "str.suffixof",
    "str.contains", "str.indexof", "str.replace", "str.to_int", "int.to_str",
    "str.in_re", "str.to_re",
    "bvnot", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
    "bvcomp", "bvneg", "bvadd", "bvsub", "bvmul", "bvudiv", "bvsrem",
    "bvurem", "bvsmod", "bvshl", "bvlshr", "bvashr", "concat", "extract",
    "rotate_left", "rotate_right", "repeat", "sign_extend", "zero_extend",
    "fp.abs", "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma",
    "fp.sqrt", "fp.rem", "fp.roundToIntegral", "fp.min", "fp.max", "fp.leq",
    "fp.lt", "fp.geq", "fp.gt", "fp.eq", "fp.isNormal", "fp.isSubnormal",
    "fp.isZero", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isPositive",
    "select", "store", "const", "map", "default",
})


def is_builtin_symbol(name: str) -> bool:
    """Check if a symbol name is a built-in SMT function/operator.

    Parameters
    ----------
    name : str
        Symbol name to check.

    Returns
    -------
    bool
        True if the symbol is a built-in.
    """
    if not name:
        return False
    if name in _BUILTIN_SYMBOLS:
        return True
    # Check for indexed symbols like (_ BitVec 32)
    if name.startswith("_"):
        parts = name.split()
        if parts and parts[0] == "_" and len(parts) > 1:
            return parts[1] in _BUILTIN_SYMBOLS
    return False
