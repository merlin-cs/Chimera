"""
SMT-LIB logic detection via Z3 AST traversal.

Single Responsibility: given an SMT2 file or Z3 expression, determine the
smallest SMT-LIB logic string (e.g. ``QF_LIA``).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Optional, Set

import z3


# ---------------------------------------------------------------------------
# Feature tracking
# ---------------------------------------------------------------------------

@dataclass
class LogicFeatures:
    """Accumulates features observed during AST traversal."""

    has_quantifiers: bool = False

    uses_int: bool = False
    uses_real: bool = False
    uses_bv: bool = False
    uses_array: bool = False
    uses_uninterpreted_sorts: bool = False
    uses_uf: bool = False

    is_nonlinear: bool = False
    is_difference_logic: bool = True  # Assumed until disproven
    has_arithmetic: bool = False

    array_index_sort: Optional[object] = field(default=None, repr=False)
    array_value_sort: Optional[object] = field(default=None, repr=False)


# ---------------------------------------------------------------------------
# Detector
# ---------------------------------------------------------------------------

_ARITH_OPS: frozenset = frozenset({
    z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS,
    z3.Z3_OP_MUL, z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM,
    z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT,
    z3.Z3_OP_TO_REAL, z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT,
})


class SMTLogicDetector:
    """Detects the SMT-LIB logic of a formula through AST traversal."""

    def __init__(self) -> None:
        self.features = LogicFeatures()
        self._visited: Set[int] = set()
        self._declared_functions: Dict[str, object] = {}

    # -- Public API ------------------------------------------------------------

    def detect_from_file(self, formula_path: str) -> str:
        """Return the SMT-LIB logic for *formula_path*."""
        solver = z3.Solver()
        formulas = z3.parse_smt2_file(formula_path, sorts={}, decls={}, ctx=solver.ctx)
        for formula in formulas:
            self._traverse(formula)
        for assertion in solver.assertions():
            self._traverse(assertion)
        self._analyze_file_declarations(formula_path)
        return self._determine_logic()

    def detect_from_formula(self, formula) -> str:
        """Return the SMT-LIB logic for a Z3 expression (or list of them)."""
        if isinstance(formula, list):
            for f in formula:
                self._traverse(f)
        else:
            self._traverse(formula)
        return self._determine_logic()

    # -- File-level heuristic analysis ----------------------------------------

    def _analyze_file_declarations(self, formula_path: str) -> None:
        try:
            content = Path(formula_path).read_text(encoding="utf-8", errors="replace")
        except OSError:
            return

        if "(Array" in content:
            self.features.uses_array = True
            if "Int" in content:
                self.features.uses_int = True
            if "Real" in content:
                self.features.uses_real = True
            if "BitVec" in content or "_ BitVec" in content:
                self.features.uses_bv = True

        if "(declare-sort" in content:
            self.features.uses_uninterpreted_sorts = True
            self.features.uses_uf = True

        for match in re.finditer(r"\(declare-fun\s+\S+\s+\(([^)]*)\)", content):
            if match.group(1).strip():
                self.features.uses_uf = True

        if "(forall" in content or "(exists" in content:
            self.features.has_quantifiers = True

        bv_ops = ("bvadd", "bvsub", "bvmul", "concat", "extract")
        if any(op in content for op in bv_ops):
            self.features.uses_bv = True

    # -- AST traversal --------------------------------------------------------

    def _traverse(self, expr) -> None:
        expr_id = id(expr)
        if expr_id in self._visited:
            return
        self._visited.add(expr_id)

        if z3.is_quantifier(expr):
            self.features.has_quantifiers = True
            self._traverse(expr.body())
            return

        if not z3.is_expr(expr):
            return

        self._detect_sort(expr)
        if z3.is_app(expr):
            self._analyze_application(expr)

        for child in expr.children():
            self._traverse(child)

    def _detect_sort(self, expr) -> None:
        try:
            sort = expr.sort()
            if z3.is_int(expr):
                self.features.uses_int = True
            elif z3.is_real(expr):
                self.features.uses_real = True
            elif z3.is_bv(expr):
                self.features.uses_bv = True
            elif z3.is_array(expr):
                self.features.uses_array = True
                if self.features.array_index_sort is None:
                    self.features.array_index_sort = sort.domain()
                    self.features.array_value_sort = sort.range()
            elif not z3.is_bool(expr):
                if sort.kind() == z3.Z3_UNINTERPRETED_SORT:
                    self.features.uses_uninterpreted_sorts = True
                    self.features.uses_uf = True
        except Exception:
            pass

    def _analyze_application(self, expr) -> None:
        decl = expr.decl()
        kind = decl.kind()
        num_args = expr.num_args()

        if kind == z3.Z3_OP_UNINTERPRETED and num_args > 0:
            self.features.uses_uf = True
            name = decl.name()
            if name not in self._declared_functions:
                self._declared_functions[name] = decl
            return

        if kind in (z3.Z3_OP_SELECT, z3.Z3_OP_STORE):
            self.features.uses_array = True
            return

        self._analyze_arithmetic(expr, kind, num_args)

    # -- Arithmetic analysis ---------------------------------------------------

    def _analyze_arithmetic(self, expr, kind: int, num_args: int) -> None:
        if kind not in _ARITH_OPS:
            return

        self.features.has_arithmetic = True

        if kind == z3.Z3_OP_MUL:
            children = expr.children()
            non_const = [c for c in children if not z3.is_int_value(c) and not z3.is_rational_value(c)]
            if len(non_const) >= 2:
                self.features.is_nonlinear = True
                self.features.is_difference_logic = False

        if kind in (z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM):
            if num_args >= 2:
                divisor = expr.arg(1)
                if not (z3.is_int_value(divisor) or z3.is_rational_value(divisor)):
                    self.features.is_nonlinear = True
            self.features.is_difference_logic = False

        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            if not self._is_difference_logic_constraint(expr):
                self.features.is_difference_logic = False
        elif kind not in (z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
            if kind in _ARITH_OPS:
                self.features.is_difference_logic = False

    # -- Difference-logic helpers ---------------------------------------------

    def _is_difference_logic_constraint(self, expr) -> bool:
        if expr.num_args() != 2:
            return False
        lhs, rhs = expr.arg(0), expr.arg(1)
        if self._is_difference(lhs) and self._is_constant(rhs):
            return True
        if self._is_constant(lhs) and self._is_difference(rhs):
            return True
        if self._is_variable(lhs) and self._is_variable(rhs):
            return True
        if self._is_variable(lhs) and self._is_constant(rhs):
            return True
        if self._is_constant(lhs) and self._is_variable(rhs):
            return True
        return False

    @staticmethod
    def _is_difference(expr) -> bool:
        if not z3.is_app(expr):
            return False
        if expr.decl().kind() != z3.Z3_OP_SUB:
            return False
        if expr.num_args() != 2:
            return False
        return SMTLogicDetector._is_variable(expr.arg(0)) and SMTLogicDetector._is_variable(expr.arg(1))

    @staticmethod
    def _is_variable(expr) -> bool:
        if z3.is_int_value(expr) or z3.is_rational_value(expr):
            return False
        return z3.is_const(expr)

    @staticmethod
    def _is_constant(expr) -> bool:
        return z3.is_int_value(expr) or z3.is_rational_value(expr)

    # -- Logic determination --------------------------------------------------

    def _determine_logic(self) -> str:  # noqa: C901 – complex but self-contained
        f = self.features
        qf = "" if f.has_quantifiers else "QF_"

        # Pure boolean / UF
        if not (f.uses_int or f.uses_real or f.uses_bv or f.uses_array):
            return f"{qf}UF"

        # Bitvector
        if f.uses_bv:
            if f.uses_array:
                return f"{qf}AUFBV" if f.uses_uf else f"{qf}ABV"
            return f"{qf}UFBV" if f.uses_uf else f"{qf}BV"

        # Array (no BV)
        if f.uses_array:
            if not f.has_arithmetic and not f.uses_uf:
                return f"{qf}AX"
            if f.uses_uf:
                if f.uses_real and f.is_nonlinear:
                    return "AUFNIRA" if f.has_quantifiers else f"{qf}AUFLIA"
                if f.uses_real:
                    return "AUFLIRA" if f.has_quantifiers else f"{qf}AUFLIA"
                if f.uses_int:
                    return "AUFLIA" if f.has_quantifiers else f"{qf}AUFLIA"
            return f"{qf}AX"

        # Arithmetic (no BV, no array)
        if f.uses_int or f.uses_real:
            return self._determine_arithmetic_logic(f, qf)

        return "UNKNOWN"

    @staticmethod
    def _determine_arithmetic_logic(f: LogicFeatures, qf: str) -> str:
        mixed = f.uses_int and f.uses_real
        int_only = f.uses_int and not f.uses_real
        real_only = f.uses_real and not f.uses_int
        quant = f.has_quantifiers

        # Difference logic
        if f.is_difference_logic and not f.is_nonlinear:
            if f.uses_uf and int_only:
                return f"{qf}UFIDL"
            if int_only:
                return f"{qf}IDL"
            if real_only:
                return f"{qf}RDL"

        # Linear
        if not f.is_nonlinear:
            if f.uses_uf:
                if int_only:
                    return "UFLIA" if quant else f"{qf}UFLIA"
                return "UFLRA" if quant else f"{qf}UFLRA"
            if int_only:
                return "LIA" if quant else f"{qf}LIA"
            if real_only:
                return "LRA" if quant else f"{qf}LRA"
            if mixed:
                return "LIRA" if quant else f"{qf}LIRA"

        # Non-linear
        if f.uses_uf:
            if int_only:
                return "UFNIA" if quant else f"{qf}UFNIA"
            return "UFNRA" if quant else f"{qf}UFNRA"
        if int_only:
            return "NIA" if quant else f"{qf}NIA"
        if real_only:
            return "NRA" if quant else f"{qf}NRA"
        if mixed:
            return "NIRA" if quant else f"{qf}NIRA"

        return "UNKNOWN"


# ---------------------------------------------------------------------------
# Convenience wrapper
# ---------------------------------------------------------------------------

def get_smt_logic(formula) -> str:
    """Determine the smallest SMT-LIB logic for *formula*.

    *formula* may be a file path (``str`` or ``Path``) or a Z3 expression.
    """
    detector = SMTLogicDetector()
    if isinstance(formula, (str, Path)):
        return detector.detect_from_file(str(formula))
    return detector.detect_from_formula(formula)
