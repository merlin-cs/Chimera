"""
Refactored SMT-LIB AST — the backbone of Chimera's formula manipulation.

Design Principles
-----------------
* Every node is a plain ``Term`` (no inheritance for Var/Const/Expr —
  those remain factory functions for backward-compatibility with the
  existing ANTLR visitor).
* Strict ``typing`` on every public symbol.
* Generic **Visitor** (read-only traversal) and **Transformer** (copy-on-
  write mutation) base classes replace the ad-hoc ``find_all`` /
  ``substitute`` methods.
* A dedicated ``HOLE`` sentinel supports skeleton extraction for
  HistFuzz and Once4All.

Re-uses (cleaned-up)
---------------------
* ``Script``, ``Term``, and the SMT command classes from the original
  ``yinyang``-derived AST — refactored for type-safety and clarity.
* ``Types`` module is imported verbatim (it is already clean).

Copyright (c) 2020-2021 The yinyang authors (original AST).
Copyright (c) 2024-2026 The Chimera authors (refactored version).
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import copy
import random
import re
from enum import Enum, auto
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
)

# ---------------------------------------------------------------------------
# SMT-LIB sort / type re-exports (unchanged from the original)
# ---------------------------------------------------------------------------
from chimera.core.types import (
    BOOLEAN_TYPE,
    REAL_TYPE,
    INTEGER_TYPE,
    STRING_TYPE,
    REGEXP_TYPE,
    ROUNDINGMODE_TYPE,
    UNKNOWN,
    BITVECTOR_TYPE,
    FP_TYPE,
    ARRAY_TYPE,
    sort2type,
    # Operator constants
    NOT,
    AND,
    OR,
    XOR,
    IMPLIES,
    IFF,
    EQUAL,
    DISTINCT,
    ITE,
)

# Type alias for SMT sort identifiers (can be ``str`` or a structured type
# like ``BITVECTOR_TYPE``).
SmtSort = Union[str, BITVECTOR_TYPE, FP_TYPE, ARRAY_TYPE]

# ---------------------------------------------------------------------------
# HOLE sentinel — marks a position in a skeleton to be filled.
# ---------------------------------------------------------------------------
HOLE_PREFIX: str = "hole"


def make_hole_name(index: int = 0) -> str:
    """Return a canonical hole identifier, e.g. ``hole 0``."""
    return f"{HOLE_PREFIX} {index}"


def is_hole(term: "Term") -> bool:
    """Return ``True`` if *term* represents a HOLE placeholder."""
    if term.op is not None and isinstance(term.op, str):
        return term.op.startswith(HOLE_PREFIX)
    return False


# ---------------------------------------------------------------------------
# TermKind — discriminated enum replacing the old boolean flags.
# ---------------------------------------------------------------------------
class TermKind(Enum):
    """Discriminator for the different roles a ``Term`` node can play."""

    VARIABLE = auto()
    CONSTANT = auto()
    EXPRESSION = auto()
    QUANTIFIER = auto()
    LET_BINDING = auto()
    LABELED = auto()
    HOLE = auto()
    UNKNOWN = auto()


# ---------------------------------------------------------------------------
# Term  (the universal AST node)
# ---------------------------------------------------------------------------
class Term:
    """Universal AST node for SMT-LIB terms.

    Backward-compatible with the original ``yinyang`` ``Term`` class while
    adding:
      * ``kind`` — a ``TermKind`` discriminator.
      * ``clone()`` — deep-copy helper.
      * ``accept(visitor)`` / ``transform(transformer)`` — double-dispatch.
      * ``depth`` / ``size`` — structural metrics.
    """

    __slots__ = (
        "name",
        "type",
        "is_const",
        "is_var",
        "label",
        "indices",
        "quantifier",
        "quantified_vars",
        "var_binders",
        "let_terms",
        "op",
        "subterms",
        "is_indexed_id",
        "parent",
    )

    def __init__(
        self,
        *,
        name: Optional[str] = None,
        type: Optional[SmtSort] = None,  # noqa: A002 — kept for compat
        is_const: Optional[bool] = None,
        is_var: Optional[bool] = None,
        label: Optional[Tuple[str, str]] = None,
        indices: Optional[List[str]] = None,
        quantifier: Optional[str] = None,
        quantified_vars: Optional[Tuple[List[str], List[str]]] = None,
        var_binders: Optional[List[str]] = None,
        let_terms: Optional[List["Term"]] = None,
        op: Optional[Union[str, "Term"]] = None,
        subterms: Optional[List[Union["Term", str]]] = None,
        is_indexed_id: bool = False,
        parent: Optional["Term"] = None,
    ) -> None:
        self._initialize(
            name=name,
            type=type,
            is_const=is_const,
            is_var=is_var,
            label=label,
            indices=indices,
            quantifier=quantifier,
            quantified_vars=quantified_vars if quantified_vars is not None else ({},),
            var_binders=var_binders,
            let_terms=let_terms,
            op=op,
            subterms=subterms,
            is_indexed_id=is_indexed_id,
            parent=parent,
        )
        self._link_parents()

    # -- low-level initialiser (used by substitute as well) ------------------

    def _initialize(
        self,
        *,
        name: Optional[str] = None,
        type: Optional[SmtSort] = None,
        is_const: Optional[bool] = None,
        is_var: Optional[bool] = None,
        label: Optional[Tuple[str, str]] = None,
        indices: Optional[List[str]] = None,
        quantifier: Optional[str] = None,
        quantified_vars: Any = None,
        var_binders: Optional[List[str]] = None,
        let_terms: Optional[List["Term"]] = None,
        op: Optional[Union[str, "Term"]] = None,
        subterms: Optional[List[Union["Term", str]]] = None,
        is_indexed_id: Optional[bool] = None,
        parent: Optional["Term"] = None,
    ) -> None:
        self.name = name
        self.type = type
        self.is_const = is_const
        self.is_var = is_var
        self.label = label
        self.indices = indices
        self.quantifier = quantifier
        self.quantified_vars = quantified_vars if quantified_vars is not None else {}
        self.var_binders = var_binders
        self.let_terms = let_terms
        self.op = op
        self.subterms = subterms
        self.is_indexed_id = is_indexed_id
        self.parent = parent

    # -- parent linkage ------------------------------------------------------

    def _link_parents(self) -> None:
        """Set the ``parent`` back-pointer on every immediate child."""
        if self.subterms:
            for child in self.subterms:
                if isinstance(child, Term):
                    child.parent = self
        if self.let_terms:
            for child in self.let_terms:
                if isinstance(child, Term):
                    child.parent = self

    # -- kind helper ---------------------------------------------------------

    @property
    def kind(self) -> TermKind:
        """Return the discriminated kind of this node."""
        if is_hole(self):
            return TermKind.HOLE
        if self.is_const:
            return TermKind.CONSTANT
        if self.is_var:
            return TermKind.VARIABLE
        if self.quantifier is not None:
            return TermKind.QUANTIFIER
        if self.var_binders is not None:
            return TermKind.LET_BINDING
        if self.label is not None:
            return TermKind.LABELED
        if self.op is not None:
            return TermKind.EXPRESSION
        return TermKind.UNKNOWN

    # -- structural metrics --------------------------------------------------

    @property
    def depth(self) -> int:
        """Return the depth of this sub-tree (leaf = 0)."""
        if not self.subterms:
            return 0
        child_depths = [
            (s.depth if isinstance(s, Term) else 0) for s in self.subterms
        ]
        return 1 + max(child_depths, default=0)

    @property
    def size(self) -> int:
        """Return the number of ``Term`` nodes in this sub-tree."""
        count = 1
        if self.subterms:
            for s in self.subterms:
                count += s.size if isinstance(s, Term) else 1
        if self.let_terms:
            for lt in self.let_terms:
                count += lt.size if isinstance(lt, Term) else 1
        return count

    # -- cloning -------------------------------------------------------------

    def clone(self) -> "Term":
        """Return a deep copy with fresh ``parent`` pointers."""
        cloned = copy.deepcopy(self)
        cloned._link_parents()
        return cloned

    # -- visitor / transformer dispatch --------------------------------------

    def accept(self, visitor: "AstVisitorBase") -> Any:
        """Double-dispatch to *visitor*.visit_<kind>(self)."""
        return visitor.visit(self)

    def transform(self, transformer: "AstTransformer") -> "Term":
        """Double-dispatch to *transformer*.transform_<kind>(self)."""
        return transformer.transform(self)

    # -- child iteration -----------------------------------------------------

    def children(self) -> Iterable["Term"]:
        """Yield all ``Term`` children (subterms + let_terms)."""
        if self.subterms:
            for s in self.subterms:
                if isinstance(s, Term):
                    yield s
        if self.let_terms:
            for lt in self.let_terms:
                if isinstance(lt, Term):
                    yield lt

    # -- traversal helpers ---------------------------------------------------

    def get_all_subterms(self) -> List["Term"]:
        """Return a flat list of every ``Term`` reachable from this node."""
        result: List[Term] = []
        if self.subterms:
            for sub in self.subterms:
                result.append(sub)
                if isinstance(sub, Term):
                    result.extend(sub.get_all_subterms())
        return result

    def find_all(self, target: "Term", accumulator: List["Term"]) -> None:
        """Append every sub-term *equal* to *target* into *accumulator*."""
        if self == target:
            accumulator.append(self)
            return
        if self.subterms:
            for sub in self.subterms:
                if isinstance(sub, Term):
                    sub.find_all(target, accumulator)

    # -- in-place substitution (backward-compatible) -------------------------

    def substitute(self, target: "Term", replacement: "Term") -> None:
        """Replace **all** occurrences of *target* with *replacement* in-place.

        This mutates the tree.  For a non-destructive version use the
        ``SubstitutionTransformer``.
        """
        occurrences: List[Term] = []
        self.find_all(target, occurrences)
        for occ in occurrences:
            saved_parent = occ.parent
            occ._initialize(
                name=copy.deepcopy(replacement.name),
                type=copy.deepcopy(replacement.type),
                is_const=copy.deepcopy(replacement.is_const),
                is_var=copy.deepcopy(replacement.is_var),
                label=copy.deepcopy(replacement.label),
                indices=copy.deepcopy(replacement.indices),
                quantifier=copy.deepcopy(replacement.quantifier),
                quantified_vars=copy.deepcopy(replacement.quantified_vars),
                var_binders=copy.deepcopy(replacement.var_binders),
                let_terms=copy.deepcopy(replacement.let_terms),
                op=copy.deepcopy(replacement.op),
                subterms=copy.deepcopy(replacement.subterms),
                is_indexed_id=copy.deepcopy(replacement.is_indexed_id),
                parent=saved_parent,
            )
            occ._link_parents()

    def substitute_n(
        self,
        target: "Term",
        replacement: "Term",
        n: int = 1,
    ) -> None:
        """Replace up to *n* randomly-chosen occurrences of *target*."""
        occurrences: List[Term] = []
        self.find_all(target, occurrences)
        chosen = random.sample(occurrences, min(n, len(occurrences)))
        for occ in chosen:
            saved_parent = occ.parent
            occ._initialize(
                name=copy.deepcopy(replacement.name),
                type=copy.deepcopy(replacement.type),
                is_const=copy.deepcopy(replacement.is_const),
                is_var=copy.deepcopy(replacement.is_var),
                label=copy.deepcopy(replacement.label),
                indices=copy.deepcopy(replacement.indices),
                quantifier=copy.deepcopy(replacement.quantifier),
                quantified_vars=copy.deepcopy(replacement.quantified_vars),
                var_binders=copy.deepcopy(replacement.var_binders),
                let_terms=copy.deepcopy(replacement.let_terms),
                op=copy.deepcopy(replacement.op),
                subterms=copy.deepcopy(replacement.subterms),
                is_indexed_id=copy.deepcopy(replacement.is_indexed_id),
                parent=saved_parent,
            )
            occ._link_parents()

    # -- equality ------------------------------------------------------------

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Term):
            return NotImplemented
        return (
            self.name == other.name
            and self.type == other.type
            and self.is_const == other.is_const
            and self.is_var == other.is_var
            and self.label == other.label
            and self.indices == other.indices
            and self.quantifier == other.quantifier
            and self.quantified_vars == other.quantified_vars
            and self.op == other.op
            and self.subterms == other.subterms
            and self.is_indexed_id == other.is_indexed_id
        )

    def __hash__(self) -> int:  # pragma: no cover — for use in sets
        return id(self)

    # -- serialisation to SMT-LIB string -------------------------------------

    def _subterms_str(self) -> str:
        if not self.subterms:
            return ""
        return " ".join(str(s) for s in self.subterms)

    def __str__(self) -> str:
        if self.is_const or self.is_var or self.is_indexed_id:
            return self.name or ""

        if self.quantifier:
            bindings = " ".join(
                f"({v} {t})"
                for v, t in zip(
                    self.quantified_vars[0],
                    self.quantified_vars[1],
                )
            )
            body = self._subterms_str()
            return f"({self.quantifier} ({bindings}) {body})"

        if self.var_binders:
            lets = "".join(
                f"({v} {self.let_terms[i]})"
                for i, v in enumerate(self.var_binders)
            )
            body = " ".join(str(s) for s in self.subterms) if self.subterms else ""
            return f"(let ({lets}) {body})"

        if self.label:
            body = self._subterms_str()
            return f"(! {body} {self.label[0]} {self.label[1]})"

        # Expression (op + subterms)
        body = self._subterms_str()
        return f"({self.op} {body})"

    def __repr__(self) -> str:
        if self.is_const:
            return self.name or "<const>"
        if self.is_var:
            return f"{self.name}:{self.type}"
        return f"Term({self.kind.name}, {self.op or self.name or '?'})"


# ---------------------------------------------------------------------------
# Factory functions (backward-compatible with the original AST visitor)
# ---------------------------------------------------------------------------

def Var(name: str, type: SmtSort, *, is_indexed_id: bool = False) -> Term:
    """Create a variable ``Term``."""
    return Term(name=name, type=type, is_var=True, is_indexed_id=is_indexed_id)


def Const(name: str, type: SmtSort = UNKNOWN, *, is_indexed_id: bool = False) -> Term:
    """Create a constant ``Term``."""
    return Term(name=name, type=type, is_const=True, is_indexed_id=is_indexed_id)


def Expr(op: Union[str, Term], subterms: List[Union[Term, str]]) -> Term:
    """Create an expression ``Term`` (op applied to subterms)."""
    return Term(op=op, subterms=subterms)


def Quantifier(
    quantifier: str,
    quantified_vars: Tuple[List[str], List[str]],
    subterms: List[Union[Term, str]],
) -> Term:
    """Create a quantified ``Term`` (``forall`` / ``exists``)."""
    return Term(quantifier=quantifier, quantified_vars=quantified_vars, subterms=subterms)


def LetBinding(
    var_binders: List[str],
    let_terms: List[Term],
    subterms: List[Union[Term, str]],
) -> Term:
    """Create a let-binding ``Term``."""
    return Term(var_binders=var_binders, let_terms=let_terms, subterms=subterms)


def LabeledTerm(label: Tuple[str, str], subterms: List[Union[Term, str]]) -> Term:
    """Create a labeled ``Term`` (``(! term :named lbl)``)."""
    return Term(label=label, subterms=subterms)


def Hole(index: int = 0) -> Term:
    """Create a HOLE placeholder ``Term`` for skeleton-based fuzzing."""
    return Expr(op=make_hole_name(index), subterms=[])


# ---------------------------------------------------------------------------
# SMT-LIB Commands
# ---------------------------------------------------------------------------

class DeclareConst:
    """``(declare-const <symbol> <sort>)``"""

    __slots__ = ("symbol", "sort")

    def __init__(self, symbol: str, sort: SmtSort) -> None:
        self.symbol = symbol
        self.sort = sort

    def __str__(self) -> str:
        return f"(declare-const {self.symbol} {self.sort})"


class DeclareFun:
    """``(declare-fun <symbol> (<input_sorts>) <output_sort>)``"""

    __slots__ = ("symbol", "input_sort", "output_sort")

    def __init__(self, symbol: str, input_sort: str, output_sort: Union[str, SmtSort]) -> None:
        self.symbol = symbol
        self.input_sort = input_sort
        self.output_sort = output_sort

    def __str__(self) -> str:
        return f"(declare-fun {self.symbol} ({self.input_sort}) {self.output_sort})"


class Assert:
    """``(assert <term>)``"""

    __slots__ = ("term",)

    def __init__(self, term: Term) -> None:
        self.term = term

    def __str__(self) -> str:
        return f"(assert {self.term})"


class AssertSoft:
    """``(assert-soft <term> <attributes>)``"""

    __slots__ = ("term", "attr")

    def __init__(self, term: Term, attr: List[Tuple[str, str]]) -> None:
        self.term = term
        self.attr = attr

    def __str__(self) -> str:
        attr_s = " ".join(f"{a[0]} {a[1]}" for a in self.attr)
        return f"(assert-soft {self.term} {attr_s})"


class Define:
    """``(define <symbol> <term>)``"""

    __slots__ = ("symbol", "term")

    def __init__(self, symbol: str, term: Term) -> None:
        self.symbol = symbol
        self.term = term

    def __str__(self) -> str:
        return f"(define {self.symbol} {self.term})"


class DefineConst:
    """``(define-const <symbol> <sort> <term>)``"""

    __slots__ = ("symbol", "sort", "term")

    def __init__(self, symbol: str, sort: SmtSort, term: Term) -> None:
        self.symbol = symbol
        self.sort = sort
        self.term = term

    def __str__(self) -> str:
        return f"(define-const {self.symbol} {self.sort} {self.term})"


class DefineFun:
    """``(define-fun <symbol> (<sorted_vars>) <sort> <term>)``"""

    __slots__ = ("symbol", "sorted_vars", "sort", "term")

    def __init__(self, symbol: str, sorted_vars: str, sort: SmtSort, term: Term) -> None:
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort
        self.term = term

    def __str__(self) -> str:
        return f"(define-fun {self.symbol} ({self.sorted_vars}) {self.sort} {self.term})"


class DefineFunRec:
    """``(define-fun-rec <symbol> (<sorted_vars>) <sort> <term>)``"""

    __slots__ = ("symbol", "sorted_vars", "sort", "term")

    def __init__(
        self, symbol: str, sorted_vars: List[str], sort: SmtSort, term: Term
    ) -> None:
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort
        self.term = term

    def __str__(self) -> str:
        svars = " ".join(self.sorted_vars) if self.sorted_vars else ""
        return f"(define-fun-rec {self.symbol} ({svars}) {self.sort} {self.term})"


class FunDecl:
    """Function declaration inside ``define-funs-rec``."""

    __slots__ = ("symbol", "sorted_vars", "sort")

    def __init__(self, symbol: str, sorted_vars: List[str], sort: SmtSort) -> None:
        self.symbol = symbol
        self.sorted_vars = sorted_vars
        self.sort = sort

    def __str__(self) -> str:
        svars = " ".join(self.sorted_vars)
        return f"({self.symbol} ({svars}) {self.sort})"


class DefineFunsRec:
    """``(define-funs-rec (<fun_decls>) (<terms>))``"""

    __slots__ = ("fun_decls", "terms")

    def __init__(self, fun_decls: List[FunDecl], terms: List[Term]) -> None:
        self.fun_decls = fun_decls
        self.terms = terms

    def __str__(self) -> str:
        decls = " ".join(str(d) for d in self.fun_decls)
        body = " ".join(str(t) for t in self.terms)
        return f"(define-funs-rec ({decls}) ({body}))"


class CheckSat:
    """``(check-sat)``"""

    __slots__ = ("terms",)

    def __init__(self, terms: Optional[List[Term]] = None) -> None:
        self.terms = terms

    def __str__(self) -> str:
        if self.terms:
            t_str = " ".join(str(t) for t in self.terms)
            return f"(check-sat {t_str})"
        return "(check-sat)"


class CheckSatAssuming:
    """``(check-sat-assuming (<terms>))``"""

    __slots__ = ("terms",)

    def __init__(self, terms: List[Term]) -> None:
        self.terms = terms

    def __str__(self) -> str:
        t_str = " ".join(str(t) for t in self.terms)
        return f"(check-sat-assuming ({t_str}))"


class GetValue:
    """``(get-value (<terms>))``"""

    __slots__ = ("terms",)

    def __init__(self, terms: List[Term]) -> None:
        self.terms = terms

    def __str__(self) -> str:
        t_str = " ".join(str(t) for t in self.terms)
        return f"(get-value ({t_str}))"


class Push:
    """``(push [<n>])``"""

    __slots__ = ("terms",)

    def __init__(self, terms: Optional[List[Term]] = None) -> None:
        self.terms = terms

    def __str__(self) -> str:
        if self.terms:
            t_str = " ".join(str(t) for t in self.terms)
            return f"(push {t_str})"
        return "(push)"


class Pop:
    """``(pop [<n>])``"""

    __slots__ = ("terms",)

    def __init__(self, terms: Optional[List[Term]] = None) -> None:
        self.terms = terms

    def __str__(self) -> str:
        if self.terms:
            t_str = " ".join(str(t) for t in self.terms)
            return f"(pop {t_str})"
        return "(pop)"


class Simplify:
    """``(simplify <term> <attrs>)``"""

    __slots__ = ("term", "attr")

    def __init__(self, term: Term, attr: List[Tuple[str, str]]) -> None:
        self.term = term
        self.attr = attr

    def __str__(self) -> str:
        attr_s = " ".join(f"{a[0]} {a[1]}" for a in self.attr)
        return f"(simplify {self.term} {attr_s})"


class Minimize:
    """``(minimize <term>)``"""

    __slots__ = ("term",)

    def __init__(self, term: Term) -> None:
        self.term = term

    def __str__(self) -> str:
        return f"(minimize {self.term})"


class Maximize:
    """``(maximize <term>)``"""

    __slots__ = ("term",)

    def __init__(self, term: Term) -> None:
        self.term = term

    def __str__(self) -> str:
        return f"(maximize {self.term})"


class Display:
    """``(display <term>)``"""

    __slots__ = ("term",)

    def __init__(self, term: Term) -> None:
        self.term = term

    def __str__(self) -> str:
        return f"(display {self.term})"


class Eval:
    """``(eval <term>)``"""

    __slots__ = ("term",)

    def __init__(self, term: Term) -> None:
        self.term = term

    def __str__(self) -> str:
        return f"(eval {self.term})"


class SMTLIBCommand:
    """Catch-all for any SMT-LIB command not handled above."""

    __slots__ = ("cmd_str",)

    def __init__(self, cmd_str: str) -> None:
        self.cmd_str = cmd_str

    def __str__(self) -> str:
        return self.cmd_str

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SMTLIBCommand):
            return NotImplemented
        return self.cmd_str == other.cmd_str

    def __hash__(self) -> int:
        return hash(self.cmd_str)


# Union type for any command that can appear in a script.
SmtCommand = Union[
    DeclareConst,
    DeclareFun,
    Assert,
    AssertSoft,
    Define,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    FunDecl,
    CheckSat,
    CheckSatAssuming,
    GetValue,
    Push,
    Pop,
    Simplify,
    Minimize,
    Maximize,
    Display,
    Eval,
    SMTLIBCommand,
]


# ---------------------------------------------------------------------------
# Script — top-level container for a parsed SMT-LIB file
# ---------------------------------------------------------------------------

class Script:
    """Top-level representation of a parsed SMT-LIB script.

    Attributes
    ----------
    commands : list[SmtCommand]
        Ordered list of all commands.
    global_vars : dict[str, SmtSort]
        Mapping from symbol name to sort for declared constants / 0-arity
        functions.
    assert_cmd : list[Assert]
        Convenience view: only the ``Assert`` commands.
    free_var_occs : list[Term]
        All free-variable occurrences found in assert bodies.
    op_occs : list[Term]
        All sub-expression occurrences (non-leaf, non-label nodes).
    const_occs : list[Term]
        All constant occurrences.
    """

    def __init__(
        self,
        commands: List[SmtCommand],
        global_vars: Dict[str, SmtSort],
    ) -> None:
        self.commands = commands
        self.global_vars = global_vars

        # Derived state (populated lazily)
        self.vars: List[Term] = []
        self.types: Dict[str, SmtSort] = {}
        self.free_var_occs: List[Term] = []
        self.op_occs: List[Term] = []
        self.const_occs: List[Term] = []
        self.assert_cmd: List[Assert] = []

        self._rebuild_indices()

    # -- index building ------------------------------------------------------

    def _rebuild_indices(self) -> None:
        """(Re-)scan ``commands`` and populate derived lists."""
        self.vars, self.types = self._extract_declarations()
        self.free_var_occs.clear()
        self.op_occs.clear()
        self.const_occs.clear()
        self.assert_cmd.clear()

        for cmd in self.commands:
            if isinstance(cmd, Assert):
                self.assert_cmd.append(cmd)
                globs = copy.copy(self.global_vars)
                self._collect_free_vars(cmd.term, globs)
                self._collect_op_occs(cmd.term)

    def _extract_declarations(self) -> Tuple[List[Term], Dict[str, SmtSort]]:
        """Return (var_list, type_map) from DeclareConst/DeclareFun commands."""
        vlist: List[Term] = []
        tmap: Dict[str, SmtSort] = {}
        for cmd in self.commands:
            if isinstance(cmd, DeclareConst):
                vlist.append(Var(cmd.symbol, cmd.sort))
                tmap[cmd.symbol] = cmd.sort
            elif isinstance(cmd, DeclareFun) and cmd.input_sort == "":
                vlist.append(Var(cmd.symbol, cmd.output_sort))
                tmap[cmd.symbol] = cmd.output_sort
        return vlist, tmap

    # -- free-variable collection --------------------------------------------

    def _collect_free_vars(self, term: Union[Term, str], scope: Dict[str, SmtSort]) -> None:
        if isinstance(term, str):
            return
        if term.is_const:
            return
        if term.label:
            return

        # Narrow scope for quantifiers
        if term.quantifier and term.quantified_vars:
            for qv in term.quantified_vars[0]:
                scope.pop(qv, None)

        # Narrow scope for let-bindings
        if term.var_binders:
            for lv in term.var_binders:
                scope.pop(lv, None)
            if term.let_terms:
                for lt in term.let_terms:
                    self._collect_free_vars(lt, scope)

        if term.is_var:
            if term.name in scope:
                self.free_var_occs.append(term)
            return

        if term.subterms:
            for sub in term.subterms:
                self._collect_free_vars(sub, scope)

    # -- operator / constant collection --------------------------------------

    def _collect_op_occs(self, term: Union[Term, str]) -> None:
        if isinstance(term, str):
            return
        if term.is_const:
            self.const_occs.append(term)
            return
        if term.label or term.is_var:
            return
        self.op_occs.append(term)
        if term.subterms:
            for sub in term.subterms:
                self._collect_op_occs(sub)

    # -- variable renaming ---------------------------------------------------

    def prefix_vars(self, prefix: str) -> None:
        """Add *prefix* to every free variable's name (declarations + uses)."""
        for cmd in self.commands:
            if isinstance(cmd, DeclareConst):
                cmd.symbol = prefix + cmd.symbol
            elif isinstance(cmd, DeclareFun) and cmd.input_sort == "":
                cmd.symbol = prefix + cmd.symbol
            elif isinstance(cmd, Assert):
                self._prefix_term(prefix, cmd.term)
        self.global_vars = {prefix + k: v for k, v in self.global_vars.items()}
        self.vars, self.types = self._extract_declarations()

    def _prefix_term(self, prefix: str, term: Union[Term, str]) -> None:
        if isinstance(term, str) or term.is_const:
            return
        if term.is_var and term.type:
            if term in self.free_var_occs:
                term.name = prefix + term.name
            return
        if term.var_binders and term.let_terms:
            for lt in term.let_terms:
                self._prefix_term(prefix, lt)
        if term.subterms:
            for sub in term.subterms:
                self._prefix_term(prefix, sub)

    def rename_vars(self) -> None:
        """Assign deterministic names to all free variables based on sort."""
        idx = 0
        name_map: Dict[str, str] = {}
        for cmd in self.commands:
            if isinstance(cmd, DeclareConst):
                new = _sort_based_name(cmd.sort, idx)
                name_map[cmd.symbol] = new
                cmd.symbol = new
                idx += 1
            elif isinstance(cmd, DeclareFun) and cmd.input_sort == "":
                new = _sort_based_name(cmd.output_sort, idx)
                name_map[cmd.symbol] = new
                cmd.symbol = new
                idx += 1
            elif isinstance(cmd, Assert):
                self._apply_name_map(name_map, cmd.term)
        self.global_vars = {
            name_map.get(k, k): v for k, v in self.global_vars.items()
        }
        self.vars, self.types = self._extract_declarations()

    def _apply_name_map(self, name_map: Dict[str, str], term: Union[Term, str]) -> None:
        if isinstance(term, str) or term.is_const:
            return
        if term.is_var and term.type and term.name in name_map:
            term.name = name_map[term.name]
            return
        if term.var_binders and term.let_terms:
            for lt in term.let_terms:
                self._apply_name_map(name_map, lt)
        if term.subterms:
            for sub in term.subterms:
                self._apply_name_map(name_map, sub)

    # -- merging asserts -----------------------------------------------------

    def merge_asserts(self) -> None:
        """Conjoin all ``Assert`` terms into a single ``(and …)`` assertion."""
        terms: List[Term] = []
        for cmd in self.commands:
            if isinstance(cmd, Assert):
                terms.append(cmd.term)
            elif isinstance(cmd, SMTLIBCommand):
                if cmd.cmd_str == "(exit)":
                    break
                if cmd.cmd_str == "(reset)":
                    terms.clear()
                if cmd.cmd_str == "(reset-assertions)":
                    terms.clear()

        if not terms:
            return

        conjunction = Assert(Term(op=AND, subterms=terms))
        new_cmds: List[SmtCommand] = []
        first_found = False
        for cmd in self.commands:
            if isinstance(cmd, Assert):
                if not first_found:
                    new_cmds.append(conjunction)
                    first_found = True
                continue
            if isinstance(cmd, SMTLIBCommand):
                if cmd.cmd_str in ("(exit)", "(reset)", "(reset-assertions)"):
                    if cmd.cmd_str == "(exit)":
                        break
                    continue
            new_cmds.append(cmd)
        self.commands = new_cmds
        self._rebuild_indices()

    # -- serialisation -------------------------------------------------------

    def __str__(self) -> str:
        return "\n".join(str(c) for c in self.commands)


# ---------------------------------------------------------------------------
# Visitor / Transformer base classes
# ---------------------------------------------------------------------------

T = TypeVar("T")


class AstVisitorBase:
    """Read-only, depth-first visitor over ``Term`` trees.

    Subclass and override ``visit_variable``, ``visit_constant``, etc.
    The default implementations recurse into children and return ``None``.

    Usage::

        class DepthCounter(AstVisitorBase[int]):
            def visit_constant(self, term): return 0
            def visit_variable(self, term): return 0
            def visit_expression(self, term):
                return 1 + max((self.visit(s) for s in term.children()), default=0)
    """

    def visit(self, term: Term) -> Any:
        """Dispatch to the appropriate ``visit_*`` method."""
        kind = term.kind
        handler = {
            TermKind.VARIABLE: self.visit_variable,
            TermKind.CONSTANT: self.visit_constant,
            TermKind.EXPRESSION: self.visit_expression,
            TermKind.QUANTIFIER: self.visit_quantifier,
            TermKind.LET_BINDING: self.visit_let_binding,
            TermKind.LABELED: self.visit_labeled,
            TermKind.HOLE: self.visit_hole,
            TermKind.UNKNOWN: self.visit_unknown,
        }.get(kind, self.visit_unknown)
        return handler(term)

    def visit_variable(self, term: Term) -> Any:
        return None

    def visit_constant(self, term: Term) -> Any:
        return None

    def visit_expression(self, term: Term) -> Any:
        return self._visit_children(term)

    def visit_quantifier(self, term: Term) -> Any:
        return self._visit_children(term)

    def visit_let_binding(self, term: Term) -> Any:
        return self._visit_children(term)

    def visit_labeled(self, term: Term) -> Any:
        return self._visit_children(term)

    def visit_hole(self, term: Term) -> Any:
        return None

    def visit_unknown(self, term: Term) -> Any:
        return self._visit_children(term)

    def _visit_children(self, term: Term) -> Any:
        for child in term.children():
            self.visit(child)
        return None


class AstTransformer:
    """Copy-on-write transformer over ``Term`` trees.

    By default, every ``transform_*`` method clones the node and recurses
    into children.  Override specific methods to replace / filter nodes.

    Usage::

        class HoleFiller(AstTransformer):
            def transform_hole(self, term):
                return my_random_term()

        filled = HoleFiller().transform(skeleton_term)
    """

    def transform(self, term: Term) -> Term:
        """Dispatch to the appropriate ``transform_*`` method."""
        kind = term.kind
        handler = {
            TermKind.VARIABLE: self.transform_variable,
            TermKind.CONSTANT: self.transform_constant,
            TermKind.EXPRESSION: self.transform_expression,
            TermKind.QUANTIFIER: self.transform_quantifier,
            TermKind.LET_BINDING: self.transform_let_binding,
            TermKind.LABELED: self.transform_labeled,
            TermKind.HOLE: self.transform_hole,
            TermKind.UNKNOWN: self.transform_unknown,
        }.get(kind, self.transform_unknown)
        return handler(term)

    def transform_variable(self, term: Term) -> Term:
        return term.clone()

    def transform_constant(self, term: Term) -> Term:
        return term.clone()

    def transform_expression(self, term: Term) -> Term:
        return self._transform_children(term)

    def transform_quantifier(self, term: Term) -> Term:
        return self._transform_children(term)

    def transform_let_binding(self, term: Term) -> Term:
        return self._transform_children(term)

    def transform_labeled(self, term: Term) -> Term:
        return self._transform_children(term)

    def transform_hole(self, term: Term) -> Term:
        return term.clone()

    def transform_unknown(self, term: Term) -> Term:
        return self._transform_children(term)

    def _transform_children(self, term: Term) -> Term:
        """Clone *term* with recursively-transformed children."""
        new = term.clone()
        if new.subterms:
            new.subterms = [
                self.transform(s) if isinstance(s, Term) else s
                for s in new.subterms
            ]
        if new.let_terms:
            new.let_terms = [
                self.transform(lt) if isinstance(lt, Term) else lt
                for lt in new.let_terms
            ]
        new._link_parents()
        return new


# ---------------------------------------------------------------------------
# Concrete visitors / transformers used across engines
# ---------------------------------------------------------------------------

class HoleCollector(AstVisitorBase):
    """Collect all ``HOLE`` terms in a tree."""

    def __init__(self) -> None:
        self.holes: List[Term] = []

    def visit_hole(self, term: Term) -> None:
        self.holes.append(term)


class VariableCollector(AstVisitorBase):
    """Collect all variable ``Term`` nodes."""

    def __init__(self) -> None:
        self.variables: List[Term] = []

    def visit_variable(self, term: Term) -> None:
        self.variables.append(term)


class SubstitutionTransformer(AstTransformer):
    """Non-destructive substitution: replace *target* with *replacement*."""

    def __init__(self, target: Term, replacement: Term) -> None:
        self._target = target
        self._replacement = replacement

    def transform(self, term: Term) -> Term:
        if term == self._target:
            return self._replacement.clone()
        return super().transform(term)


class SkeletonExtractor(AstTransformer):
    """Replace atomic (non-connective) sub-terms with ``HOLE`` placeholders.

    This is the core skeleton-extraction logic used by both HistFuzz and
    Once4All.

    Parameters
    ----------
    connectives : frozenset[str]
        Operators that are considered "structural" (not replaced).
        Defaults to the standard Boolean connectives.
    rename_quantified : bool
        If ``True``, rename quantified variables to ``VAR0``, ``VAR1``, …
        and their sorts to ``TYPE0``, ``TYPE1``, … (HistFuzz convention).
    """

    BOOLEAN_CONNECTIVES: FrozenSet[str] = frozenset({
        NOT, AND, OR, XOR, IMPLIES, IFF,
    })

    def __init__(
        self,
        *,
        connectives: Optional[FrozenSet[str]] = None,
        rename_quantified: bool = False,
    ) -> None:
        self._connectives = connectives or self.BOOLEAN_CONNECTIVES
        self._rename = rename_quantified
        self._hole_counter: int = 0

    def transform_expression(self, term: Term) -> Term:
        """Recurse into connectives; replace everything else with a HOLE."""
        if isinstance(term.op, str) and term.op in self._connectives:
            return self._transform_children(term)
        return self._make_hole()

    def transform_quantifier(self, term: Term) -> Term:
        new = self._transform_children(term)
        if self._rename and new.quantified_vars:
            qvars, qtypes = new.quantified_vars
            new.quantified_vars = (
                [f"VAR{i}" for i in range(len(qvars))],
                [f"TYPE{i}" for i in range(len(qtypes))],
            )
        return new

    def transform_variable(self, term: Term) -> Term:
        return self._make_hole()

    def transform_constant(self, term: Term) -> Term:
        return self._make_hole()

    def _make_hole(self) -> Term:
        h = Hole(self._hole_counter)
        self._hole_counter += 1
        return h


# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

_SORT_NAME_RE = re.compile(r"[^a-zA-Z0-9]")


def _sort_based_name(sort: SmtSort, index: int) -> str:
    """Generate a deterministic variable name from *sort* and *index*.

    Examples: ``int_0``, ``bv32_1``, ``array_2_Int_Real``.
    """
    sort_str = str(sort)
    if sort_str.startswith("(Array"):
        # (Array <idx_sort> <elem_sort>) → array_<i>_<idx>_<elem>
        parts = _extract_outer_parenthesis(sort_str.strip("(").strip(")"))
        idx_s = _SORT_NAME_RE.sub("", parts[1] if len(parts) > 1 else "?")
        elem_s = _SORT_NAME_RE.sub("", parts[2] if len(parts) > 2 else "?")
        return f"array_{index}_{idx_s}_{elem_s}"
    if "Float" in sort_str or "FP" in sort_str:
        digits = re.sub(r"\D", "", sort_str)
        return f"fp{digits}_{index}"
    if "BitVec" in sort_str:
        digits = re.sub(r"\D", "", sort_str)
        return f"bv{digits}_{index}"
    return f"{sort_str.lower()}_{index}"


def _extract_outer_parenthesis(s: str) -> List[str]:
    """Split *s* into top-level parenthesised groups and bare tokens.

    Cleaned-up version of the original ``extract_outer_parenthesis``.
    """
    result: List[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(s):
        if ch == "(":
            if depth == 0:
                token = s[start:i].strip()
                if token:
                    result.append(token)
                start = i
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                result.append(s[start : i + 1])
                start = i + 1
    tail = s[start:].strip()
    if tail:
        result.extend(tail.split())
    return result


def collect_basic_subterms(
    term: Union[Term, "Assert"],
    assert_index: int = 0,
    *,
    rename_quantified: bool = False,
) -> Tuple[List[Tuple[Term, int]], List[Optional[SmtSort]]]:
    """Return the atomic (non-connective) sub-terms of *term*.

    This is a cleaned-up version of the original ``get_basic_subterms``.

    Returns
    -------
    (subterm_list, type_list)
        Each element of *subterm_list* is ``(term, assert_index)`` so we
        know which assertion it belongs to.
    """
    basics: List[Tuple[Term, int]] = []
    types: List[Optional[SmtSort]] = []

    _CONNECTIVES = frozenset({NOT, AND, OR, XOR, IMPLIES, IFF})

    def _walk(node: Union[Term, str, Any], idx: int) -> None:
        if isinstance(node, str):
            return
        if isinstance(node, Term):
            if (
                (node.op in _CONNECTIVES)
                or node.quantifier is not None
                or node.let_terms is not None
            ):
                if node.quantifier is not None and rename_quantified:
                    qvars, qtypes = node.quantified_vars
                    for vi in range(len(qvars)):
                        qvars[vi] = f"VAR{vi}"
                    for ti in range(len(qtypes)):
                        qtypes[ti] = f"TYPE{ti}"
                if node.subterms:
                    for sub in node.subterms:
                        _walk(sub, idx)
            else:
                basics.append((node, idx))
                types.append(node.type)
        elif hasattr(node, "term"):
            _walk(node.term, idx)

    if isinstance(term, Assert):
        _walk(term.term, assert_index)
    else:
        _walk(term, assert_index)
    return basics, types


def collect_all_basic_subformulas(
    script: Script,
    *,
    rename_quantified: bool = False,
) -> List[Tuple[Term, int]]:
    """Return all atomic sub-formulas across every ``Assert`` in *script*.

    Clean replacement for the old ``get_all_basic_subformula``.
    """
    result: List[Tuple[Term, int]] = []
    for i, cmd in enumerate(script.assert_cmd):
        basics, _ = collect_basic_subterms(cmd, i, rename_quantified=rename_quantified)
        result.extend(basics)
    return result
