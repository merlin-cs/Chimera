"""
SMT logic analysis and compatibility checking.

This module provides utilities for analyzing SMT-LIB logic strings and
determining compatibility between formulas and solver logic capabilities.

The logic analysis is based on the SMT-LIB standard logic naming conventions:
- QF_ prefix indicates quantifier-free logics
- Theory suffixes: BV (bitvectors), FP (floating-point), A (arrays), etc.
- Arithmetic suffixes: IA (integers), RA (reals), etc.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Flag, auto
from typing import Any, FrozenSet, Optional, Set


class LogicCapability(Flag):
    """Bitflags representing features supported by an SMT logic."""

    NONE = 0
    QUANTIFIER_FREE = auto()      # QF_ prefix - no quantifiers allowed
    QUANTIFIERS = auto()          # Quantifiers allowed (no QF_ prefix)
    BITVECTORS = auto()           # BV theory
    FLOATING_POINT = auto()       # FP theory
    ARRAYS = auto()               # Array theory
    INTEGERS = auto()             # Integer arithmetic
    REALS = auto()                # Real arithmetic
    NONLINEAR = auto()            # Nonlinear arithmetic
    DIFFERENCE_LOGIC = auto()     # Difference logic (IDL, RDL)
    UNINTERPRETED_FUNCS = auto()  # UF theory
    STRINGS = auto()              # String theory
    SEQUENCES = auto()            # Seq theory


@dataclass(frozen=True)
class LogicInfo:
    """Parsed information about an SMT-LIB logic string.

    Attributes
    ----------
    name : str
        The original logic name (e.g., "QF_LIA", "AUFLIA").
    capabilities : LogicCapability
        Bitflags of supported features.
    is_quantifier_free : bool
        True if the logic has QF_ prefix.
    theories : FrozenSet[str]
        Set of theory names extracted from the logic string.
    """

    name: str
    capabilities: LogicCapability
    is_quantifier_free: bool
    theories: FrozenSet[str] = field(default_factory=frozenset)

    def supports(self, feature: LogicCapability) -> bool:
        """Check if this logic supports a given feature."""
        return bool(self.capabilities & feature)

    def __str__(self) -> str:
        return self.name


def detect_script_logic(script: Any) -> str:
    """Infer a canonical SMT-LIB logic name from a parsed script.

    The history collector and extractor both need a conservative fallback
    when a script does not declare ``set-logic``.  Keeping that fallback here
    prevents the two pipelines from drifting into different classifications.
    Explicit ``set-logic`` commands always win; structural inference is only
    used when no declaration is present.
    """
    text = str(script)
    explicit = re.search(r"\(set-logic\s+([^\s()]+)\)", text, re.IGNORECASE)
    if explicit:
        return explicit.group(1).upper()

    lowered = text.lower()
    quantified = "forall" in lowered or "exists" in lowered
    has_bv = "bitvec" in lowered or re.search(r"\bbv[a-z0-9_.-]*\b", lowered) is not None
    has_fp = "floatingpoint" in lowered or re.search(r"\bfp[.]", lowered) is not None
    has_arrays = any(token in lowered for token in ("array", "select", "store"))
    has_strings = "string" in lowered or "str." in lowered
    has_sequences = "seq." in lowered or "sequence" in lowered
    has_int = "int" in lowered or "to_int" in lowered
    has_real = "real" in lowered or "to_real" in lowered
    has_nonlinear = bool(re.search(r"\(\s*\*\s+", text)) and (has_int or has_real)

    has_uf = False
    for command in getattr(script, "commands", ()):  # avoid importing AST types
        if command.__class__.__name__ == "DeclareFun" and getattr(command, "input_sort", ""):
            has_uf = True
            break

    parts: list[str] = []
    if has_arrays:
        parts.append("A")
    if has_uf:
        parts.append("UF")
    if has_int and has_real:
        parts.append("NIRA" if has_nonlinear else "LIRA")
    elif has_int:
        parts.append("NIA" if has_nonlinear else "LIA")
    elif has_real:
        parts.append("NRA" if has_nonlinear else "LRA")
    if has_bv:
        parts.append("BV")
    if has_fp:
        parts.append("FP")
    if has_strings:
        parts.append("S")
    if has_sequences:
        parts.append("SEQ")

    body = "".join(parts) or "UF"
    return body if quantified else f"QF_{body}"


# Regular expression patterns for logic parsing
_QUANTIFIER_FREE_PATTERN = re.compile(r"^QF_(.+)$")
_ARITHMETIC_PATTERN = re.compile(r"(IRA?|IA|RA?|NIA|NRA|IDL|RDL)")
_BITVECTOR_PATTERN = re.compile(r"BV")
_ARRAY_PATTERN = re.compile(r"(?:^|[^LR])A(?:[^LR]|$)")  # A not preceded/followed by I/R
_FP_PATTERN = re.compile(r"FP")
_UF_PATTERN = re.compile(r"UF")
_STRING_PATTERN = re.compile(r"S(?!EQ)")  # S not followed by EQ (sequences)
_SEQ_PATTERN = re.compile(r"SEQ")


def parse_logic(logic_name: str) -> LogicInfo:
    """Parse an SMT-LIB logic name into structured information.

    Parameters
    ----------
    logic_name : str
        The logic name to parse (e.g., "QF_LIA", "AUFLIA", "BV").

    Returns
    -------
    LogicInfo
        Structured information about the logic's capabilities.

    Examples
    --------
    >>> info = parse_logic("QF_LIA")
    >>> info.is_quantifier_free
    True
    >>> info.supports(LogicCapability.INTEGERS)
    True
    >>> info.supports(LogicCapability.BITVECTORS)
    False
    """
    name = logic_name.upper().strip()
    capabilities = LogicCapability.NONE
    theories: Set[str] = set()

    # Check quantifier-free prefix
    is_qf = False
    match = _QUANTIFIER_FREE_PATTERN.match(name)
    if match:
        is_qf = True
        capabilities |= LogicCapability.QUANTIFIER_FREE
        body = match.group(1)
    else:
        capabilities |= LogicCapability.QUANTIFIERS
        body = name

    # Extract theories from the body
    # Bitvectors
    if _BITVECTOR_PATTERN.search(body):
        capabilities |= LogicCapability.BITVECTORS
        theories.add("BV")

    # Floating-point
    if _FP_PATTERN.search(body):
        capabilities |= LogicCapability.FLOATING_POINT
        theories.add("FP")

    # Arrays - be careful to not match 'A' in 'LIA', 'RA', etc.
    # Check for 'A' that's not part of 'IA', 'RA', 'IRA'
    temp_body = body
    for suffix in ("IRA", "IA", "RA"):
        temp_body = temp_body.replace(suffix, "")
    if "A" in temp_body:
        capabilities |= LogicCapability.ARRAYS
        theories.add("Array")

    # Integer arithmetic
    if "IRA" in body:
        capabilities |= LogicCapability.INTEGERS | LogicCapability.REALS
        theories.add("Int")
        theories.add("Real")
    elif "IA" in body or "IDL" in body:
        capabilities |= LogicCapability.INTEGERS
        theories.add("Int")
    elif "RA" in body or "RDL" in body:
        capabilities |= LogicCapability.REALS
        theories.add("Real")

    # Difference logic
    if "IDL" in body:
        capabilities |= LogicCapability.DIFFERENCE_LOGIC | LogicCapability.INTEGERS
    elif "RDL" in body:
        capabilities |= LogicCapability.DIFFERENCE_LOGIC | LogicCapability.REALS

    # Nonlinear arithmetic
    if "N" in body and ("IA" in body or "RA" in body):
        capabilities |= LogicCapability.NONLINEAR

    # Uninterpreted functions
    if _UF_PATTERN.search(body):
        capabilities |= LogicCapability.UNINTERPRETED_FUNCS
        theories.add("UF")

    # Strings
    if _STRING_PATTERN.search(body):
        capabilities |= LogicCapability.STRINGS
        theories.add("String")

    # Sequences
    if _SEQ_PATTERN.search(body):
        capabilities |= LogicCapability.SEQUENCES
        theories.add("Seq")

    return LogicInfo(
        name=logic_name,
        capabilities=capabilities,
        is_quantifier_free=is_qf,
        theories=frozenset(theories),
    )


def is_logic_compatible(source_logic: str, target_logic: str) -> bool:
    """Check if a formula from source_logic can be used in target_logic.

    A formula is compatible if the target logic supports all features required
    by the source formula.

    Parameters
    ----------
    source_logic : str
        Logic of the formula to insert.
    target_logic : str
        Target logic context.

    Returns
    -------
    bool
        True if the source formula is compatible with target logic.

    Examples
    --------
    >>> is_logic_compatible("QF_LIA", "QF_LIA")
    True
    >>> is_logic_compatible("LIA", "QF_LIA")  # Quantifiers not allowed in QF
    False
    >>> is_logic_compatible("QF_BV", "QF_LIA")  # BV requires BV theory
    False
    """
    if source_logic == target_logic:
        return True

    source = parse_logic(source_logic)
    target = parse_logic(target_logic)

    # Quantifier-free constraint
    # If target is QF and source has quantifiers, incompatible
    if target.is_quantifier_free and source.supports(LogicCapability.QUANTIFIERS):
        return False

    # Theory requirements
    # Source can only use theories that target supports
    if source.supports(LogicCapability.BITVECTORS) and not target.supports(LogicCapability.BITVECTORS):
        return False

    if source.supports(LogicCapability.FLOATING_POINT) and not target.supports(LogicCapability.FLOATING_POINT):
        return False

    if source.supports(LogicCapability.ARRAYS) and not target.supports(LogicCapability.ARRAYS):
        return False

    # Arithmetic compatibility
    if source.supports(LogicCapability.INTEGERS) and not target.supports(LogicCapability.INTEGERS):
        return False

    if source.supports(LogicCapability.REALS) and not target.supports(LogicCapability.REALS):
        return False

    # Nonlinearity
    if source.supports(LogicCapability.NONLINEAR) and not target.supports(LogicCapability.NONLINEAR):
        return False

    # Difference logic is more restrictive
    source_is_diff = source.supports(LogicCapability.DIFFERENCE_LOGIC)
    target_is_diff = target.supports(LogicCapability.DIFFERENCE_LOGIC)
    source_is_arith = source.supports(LogicCapability.INTEGERS) or source.supports(LogicCapability.REALS)
    source_is_linear = source_is_arith and not source.supports(LogicCapability.NONLINEAR) and not source_is_diff

    if source_is_linear and target_is_diff:
        return False

    # Uninterpreted functions
    if source.supports(LogicCapability.UNINTERPRETED_FUNCS) and not target.supports(LogicCapability.UNINTERPRETED_FUNCS):
        return False

    # Strings
    if source.supports(LogicCapability.STRINGS) and not target.supports(LogicCapability.STRINGS):
        return False

    # Sequences
    if source.supports(LogicCapability.SEQUENCES) and not target.supports(LogicCapability.SEQUENCES):
        return False

    return True


def get_compatible_logics(source_logic: str, available_logics: FrozenSet[str]) -> FrozenSet[str]:
    """Find all logics compatible with the source logic.

    Parameters
    ----------
    source_logic : str
        Logic of the formula to insert.
    available_logics : FrozenSet[str]
        Set of available target logics.

    Returns
    -------
    FrozenSet[str]
        Subset of available_logics that are compatible with source_logic.
    """
    return frozenset(
        logic for logic in available_logics
        if is_logic_compatible(source_logic, logic)
    )


# Built-in SMT-LIB sorts (don't need declare-sort)
BUILTIN_SORTS: FrozenSet[str] = frozenset({
    "Bool",
    "Int",
    "Real",
    "String",
    "RegLan",
    "RoundingMode",
    "Seq",
    # Indexed families (base names)
    "BitVec",
    "FloatingPoint",
    "Float16",
    "Float32",
    "Float64",
    "Float128",
    "Array",
})


def is_builtin_sort(sort_name: str) -> bool:
    """Check if a sort name is a built-in SMT-LIB sort.

    Parameters
    ----------
    sort_name : str
        The sort name to check.

    Returns
    -------
    bool
        True if the sort is built-in and doesn't need declaration.

    Examples
    --------
    >>> is_builtin_sort("Int")
    True
    >>> is_builtin_sort("(_ BitVec 32)")
    True
    >>> is_builtin_sort("MyCustomSort")
    False
    """
    name = sort_name.strip()

    # Direct match
    if name in BUILTIN_SORTS:
        return True

    # Indexed family: (_ BitVec 32) → base name is BitVec
    if name.startswith("(_"):
        parts = name.replace(")", "").split()
        if len(parts) >= 2 and parts[1] in BUILTIN_SORTS:
            return True

    # Parametric sort written inline: (Array Int Int)
    if name.startswith("("):
        inner = name.lstrip("(").split()[0]
        if inner in BUILTIN_SORTS:
            return True

    return False


def extract_sorts_from_declaration(decl_str: str) -> Set[str]:
    """Extract sort names from a declaration string.

    Parameters
    ----------
    decl_str : str
        Declaration string like "(declare-fun f (Int Bool) Int)".

    Returns
    -------
    Set[str]
        Set of non-built-in sort names that would need declare-sort.

    Examples
    --------
    >>> extract_sorts_from_declaration("(declare-fun f (Int MySort) MySort)")
    {'MySort'}
    >>> extract_sorts_from_declaration("(declare-fun x () Int)")
    set()
    """
    sorts: Set[str] = set()

    # Match the command keyword and symbol name
    match = re.match(
        r'\((?:declare-fun|define-fun|declare-const|define-const)\s+\S+\s*',
        decl_str
    )
    if not match:
        return sorts

    remainder = decl_str[match.end():]
    is_define = 'define-fun' in decl_str or 'define-const' in decl_str

    # Tokenize: split by whitespace and parens, keeping paren chars
    tokens = re.findall(r'[()]|[^\s()]+', remainder)

    # For define-fun, skip the parameter list ((x S1) (y S2) ...)
    # and only process the return sort (not the body)
    idx = 0
    if is_define:
        # Skip opening ((
        if idx < len(tokens) and tokens[idx] == '(':
            idx += 1
        if idx < len(tokens) and tokens[idx] == '(':
            idx += 1
        # Skip to matching ))
        depth = 2
        while idx < len(tokens) and depth > 0:
            if tokens[idx] == '(':
                depth += 1
            elif tokens[idx] == ')':
                depth -= 1
            idx += 1
        # Now tokens[idx] should be the return sort
        if idx < len(tokens):
            tok = tokens[idx]
            if tok not in ('(', ')', '_') and not tok.isdigit() and not is_builtin_sort(tok):
                sorts.add(tok)
        return sorts

    # For declare-fun/declare-const, process all tokens (parameter sorts + return sort)
    for tok in tokens:
        if tok in ('(', ')') or tok == '_':
            continue
        if tok.isdigit():
            continue
        if tok in ('!', ':named', 'NUMERAL', 'par'):
            continue
        if not is_builtin_sort(tok):
            sorts.add(tok)

    return sorts
