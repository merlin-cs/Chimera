"""
Logic-aware extraction pipeline for HistFuzz.

This module provides the LogicAwareExtractor class that extracts skeletons
and building blocks from historical bug-triggering formulas, classifying
them by SMT-LIB logic and preserving all necessary context.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import os
import re
import sys
from dataclasses import dataclass

# Increase recursion limit to handle deeply nested ASTs (some formulas have depth > 2000,
# and str() on a Script with such ASTs requires ~5000+ stack frames in _prepare_seed)
sys.setrecursionlimit(100000)
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from chimera.core.smt_ast import (
    Script,
    Term,
    Assert,
    DeclareConst,
    DeclareFun,
    SkeletonExtractor,
    collect_all_basic_subformulas,
)
from chimera.core.smt_parser import parse_file, parse_string
from chimera.core.logic_analyzer import parse_logic, LogicCapability
from chimera.history.corpus import Corpus, BuildingBlock, Skeleton, FuncInfo

logger = logging.getLogger(__name__)


@dataclass
class FileExtraction:
    """Result of extracting skeletons and blocks from a single file.

    Attributes
    ----------
    logic : str
        Inferred or provided logic for this file.
    skeletons : List[Skeleton]
        Extracted skeletons with context.
    blocks : List[BuildingBlock]
        Extracted building blocks with context.
    parse_errors : List[str]
        Any errors encountered during parsing.
    """
    logic: str
    skeletons: List[Skeleton]
    blocks: List[BuildingBlock]
    parse_errors: List[str]


class LogicAwareExtractor:
    """Extract skeletons and building blocks with logic classification.

    This extractor improves upon the legacy extraction by:
    1. Preserving original variable names (not renaming to var0, var1)
    2. Tracking sort/function dependencies per item
    3. Inferring logic from formula structure using logic_analyzer
    4. Separating quantified vs QF skeletons within each logic
    5. Validating during extraction - rejecting malformed formulas

    Parameters
    ----------
    logic_mapping : Dict[str, List[str]], optional
        Pre-computed logic-to-files mapping. If None, logic is inferred
        from formula structure.
    """

    def __init__(
        self,
        logic_mapping: Optional[Dict[str, List[str]]] = None,
    ) -> None:
        self._logic_mapping = logic_mapping
        self._file_to_logic: Dict[str, str] = {}

        # Build reverse mapping: file -> logic
        if logic_mapping:
            for logic, files in logic_mapping.items():
                for f in files:
                    self._file_to_logic[f] = logic.upper()

        # Statistics
        self._stats = {
            "files_processed": 0,
            "files_failed": 0,
            "skeletons_extracted": 0,
            "blocks_extracted": 0,
            "files_with_quantifiers": 0,
        }

    def extract_all(
        self,
        file_paths: List[str],
        progress_callback: Optional[callable] = None,
    ) -> Corpus:
        """Extract skeletons and blocks from all files.

        Parameters
        ----------
        file_paths : List[str]
            List of .smt2 file paths to process.
        progress_callback : callable, optional
            Called with (current, total, logic) after each file.

        Returns
        -------
        Corpus
            Logic-classified corpus of extracted items.
        """
        corpus = Corpus()
        total = len(file_paths)

        for i, path in enumerate(file_paths):
            logic = self._get_logic_for_file(path)
            extraction = self._extract_from_file(path, logic)

            if extraction.parse_errors:
                self._stats["files_failed"] += 1
                for err in extraction.parse_errors:
                    logger.warning("File %s: %s", path, err)
            else:
                self._stats["files_processed"] += 1
                self._stats["skeletons_extracted"] += len(extraction.skeletons)
                self._stats["blocks_extracted"] += len(extraction.blocks)

                if any(s.is_quantified for s in extraction.skeletons):
                    self._stats["files_with_quantifiers"] += 1

            for skel in extraction.skeletons:
                corpus.add_skeleton(skel)
            for block in extraction.blocks:
                corpus.add_block(block)

            if progress_callback:
                progress_callback(i + 1, total, logic)

        corpus.metadata["extraction_stats"] = self._stats
        logger.info(
            "Extraction complete: %d files, %d skeletons, %d blocks",
            self._stats["files_processed"],
            self._stats["skeletons_extracted"],
            self._stats["blocks_extracted"],
        )
        return corpus

    def _get_logic_for_file(self, path: str) -> str:
        """Get logic for a file, using mapping or inference."""
        # Check pre-computed mapping first
        if path in self._file_to_logic:
            return self._file_to_logic[path]

        # Fall back to inference from directory structure
        # e.g., .../QF_LIA/formula.smt2 -> QF_LIA
        parts = Path(path).parts
        for part in reversed(parts):
            if self._is_valid_logic_name(part):
                return part.upper()

        # Default to UNKNOWN
        return "UNKNOWN"

    def _is_valid_logic_name(self, name: str) -> bool:
        """Check if a string looks like an SMT-LIB logic name."""
        name = name.upper()
        # Common logic patterns
        patterns = [
            r"^QF_",  # Quantifier-free
            r"^LIA$", r"^LRA$", r"^NIA$", r"^NRA$",  # Arithmetic
            r"^BV$", r"^FP$",  # Theories
            r"^UF",  # Uninterpreted functions
            r"^IDL$", r"^RDL$",  # Difference logic
            r"^AUFLIA$", r"^AUFLRA$", r"^AUFNIA$",  # Array + UF
            r"^UFLIA$", r"^UFLRA$", r"^UFNIA$",
            r"^AX$", r"^ABV$",
        ]
        return any(re.match(p, name) for p in patterns)

    def _extract_from_file(self, path: str, logic: str) -> FileExtraction:
        """Extract skeletons and blocks from a single file.

        Parameters
        ----------
        path : str
            Path to .smt2 file.
        logic : str
            Logic classification for extracted items.

        Returns
        -------
        FileExtraction
            Extracted items with context.
        """
        parse_errors = []

        # Parse the file
        result = parse_file(path, silent=True)
        if result is None:
            return FileExtraction(
                logic=logic,
                skeletons=[],
                blocks=[],
                parse_errors=[f"Failed to parse {path}"],
            )

        script, global_vars = result

        # Validate basic structure
        if not script or not script.assert_cmd:
            return FileExtraction(
                logic=logic,
                skeletons=[],
                blocks=[],
                parse_errors=[f"No assertions found in {path}"],
            )

        # Collect declarations for context
        var_decls, func_decls = self._collect_declarations(script)

        # Infer logic from structure if not provided
        if logic == "UNKNOWN":
            logic = self._infer_logic(script)

        # Extract skeletons (one per assertion)
        skeletons = self._extract_skeletons(
            script, logic, var_decls, func_decls
        )

        # Extract building blocks (atomic subformulas)
        blocks = self._extract_building_blocks(
            script, logic, var_decls, func_decls
        )

        return FileExtraction(
            logic=logic,
            skeletons=skeletons,
            blocks=blocks,
            parse_errors=parse_errors,
        )

    def _collect_declarations(
        self, script: Script
    ) -> Tuple[Dict[str, str], Dict[str, FuncInfo]]:
        """Collect variable and function declarations from a script.

        Returns
        -------
        var_decls : Dict[str, str]
            {variable_name: sort_string}
        func_decls : Dict[str, FuncInfo]
            {function_name: FuncInfo}
        """
        var_decls: Dict[str, str] = {}
        func_decls: Dict[str, FuncInfo] = {}

        for cmd in script.commands:
            if isinstance(cmd, DeclareConst):
                var_decls[cmd.symbol] = str(cmd.sort)

            elif isinstance(cmd, DeclareFun):
                # Parse function signature
                # For 0-arity functions (constants), input_sort is ""
                if cmd.input_sort == "":
                    # Constant: (declare-const name sort)
                    func_decls[cmd.symbol] = FuncInfo(
                        name=cmd.symbol,
                        arg_sorts=[],
                        ret_sort=str(cmd.output_sort),
                    )
                else:
                    # Function: parse input_sort string like "(Int Bool)"
                    arg_sorts = self._parse_sort_list(cmd.input_sort)
                    func_decls[cmd.symbol] = FuncInfo(
                        name=cmd.symbol,
                        arg_sorts=arg_sorts,
                        ret_sort=str(cmd.output_sort),
                    )

        return var_decls, func_decls

    def _parse_sort_list(self, sort_str: str) -> List[str]:
        """Parse a sort list string like \"(Int Bool)\" -> [\"Int\", \"Bool\"]."""
        sort_str = sort_str.strip()
        if sort_str.startswith("(") and sort_str.endswith(")"):
            sort_str = sort_str[1:-1]

        # Split by whitespace, handling nested parens
        result = []
        depth = 0
        current = ""

        for ch in sort_str:
            if ch == "(":
                depth += 1
                current += ch
            elif ch == ")":
                depth -= 1
                current += ch
            elif ch.isspace() and depth == 0:
                if current.strip():
                    result.append(current.strip())
                current = ""
            else:
                current += ch

        if current.strip():
            result.append(current.strip())

        return result

    def _infer_logic(self, script: Script) -> str:
        """Infer logic from formula structure.

        Analyzes:
        - Quantifiers (QF vs quantified)
        - Theories used (BV, FP, Arrays, UF)
        - Arithmetic types (Int, Real, nonlinear)

        Returns
        -------
        str
            Inferred logic name (e.g., "QF_LIA", "AUFLIA")
        """
        has_quantifiers = False
        has_bv = False
        has_fp = False
        has_arrays = False
        has_uf = False
        has_int = False
        has_real = False
        has_nonlinear = False

        script_str = str(script)

        # Check for quantifiers
        has_quantifiers = "forall" in script_str or "exists" in script_str

        # Check for theories
        has_bv = "BitVec" in script_str or "bv" in script_str
        has_fp = "FloatingPoint" in script_str or "fp" in script_str
        has_arrays = "Array" in script_str or "select" in script_str or "store" in script_str

        # Check for UF (uninterpreted functions)
        # Look for declare-fun with non-empty argument list
        for cmd in script.commands:
            if isinstance(cmd, DeclareFun) and cmd.input_sort != "":
                has_uf = True
                break

        # Check for arithmetic
        has_int = "Int" in script_str or "to_int" in script_str
        has_real = "Real" in script_str or "to_real" in script_str

        # Check for nonlinear (multiplication of variables)
        # This is a heuristic - real detection would need AST analysis
        has_nonlinear = "* " in script_str and (has_int or has_real)

        # Build logic name
        parts = []

        if not has_quantifiers:
            parts.append("QF")

        if has_arrays:
            parts.append("A")

        if has_uf:
            if not parts or parts[-1] != "QF":
                parts.append("UF")
            elif parts == ["QF"]:
                parts.append("UF")

        # Arithmetic suffix
        if has_int and has_real:
            if has_nonlinear:
                parts.append("NIRA")
            else:
                parts.append("LIRA")
        elif has_int:
            if has_nonlinear:
                parts.append("NIA")
            else:
                parts.append("LIA")
        elif has_real:
            if has_nonlinear:
                parts.append("NRA")
            else:
                parts.append("LRA")

        # Theories
        if has_bv:
            parts.append("BV")

        if has_fp:
            parts.append("FP")

        # Build final name
        if not parts:
            return "UF"  # Default to pure UF

        # Rearrange to standard form
        logic = "".join(parts)

        # Normalize common patterns
        if logic.startswith("QF") and "UF" not in logic and len(parts) == 2:
            # QF + theory without UF -> add UF implicitly
            logic = logic[:2] + "UF" + logic[2:]

        return logic

    def _extract_skeletons(
        self,
        script: Script,
        logic: str,
        var_decls: Dict[str, str],
        func_decls: Dict[str, FuncInfo],
    ) -> List[Skeleton]:
        """Extract skeletons from all assertions in a script.

        Each assertion becomes a skeleton with atomic subterms replaced
        by HOLE placeholders.
        """
        skeletons = []
        extractor = SkeletonExtractor(rename_quantified=True)

        for cmd in script.assert_cmd:
            try:
                # Transform assertion term into skeleton
                skeleton_term = extractor.transform(cmd.term)

                # Check for quantifiers
                is_quantified = self._term_has_quantifier(cmd.term)

                # Collect hole types by walking the skeleton
                from chimera.core.smt_ast import HoleCollector
                collector = HoleCollector()
                collector.visit(skeleton_term)
                hole_types = [
                    str(h.type) if h.type else "Bool"
                    for h in collector.holes
                ]

                # Collect sort dependencies from the original term
                sort_deps = self._collect_sort_deps(cmd.term)

                # Create skeleton
                skeleton = Skeleton(
                    term_smt2=str(skeleton_term),
                    logic=logic,
                    is_quantified=is_quantified,
                    hole_types=hole_types,
                    sort_deps=sort_deps,
                    func_deps=set(func_decls.keys()),
                    var_decls=var_decls,
                    func_decls=func_decls,
                )
                skeletons.append(skeleton)

            except Exception as e:
                logger.warning("Failed to extract skeleton: %s", e)
                continue

        return skeletons

    def _extract_building_blocks(
        self,
        script: Script,
        logic: str,
        var_decls: Dict[str, str],
        func_decls: Dict[str, FuncInfo],
    ) -> List[BuildingBlock]:
        """Extract atomic building blocks from a script.

        Returns all non-connective subterms that can be used to fill
        skeleton holes.

        For variable-free terms, logic is inferred from the operators used
        rather than inherited from the source file.
        """
        blocks = []
        basics = collect_all_basic_subformulas(script, rename_quantified=False)

        for term, _assert_idx in basics:
            try:
                # Collect sort dependencies
                sort_deps = self._collect_sort_deps(term)

                # Collect function dependencies
                func_deps = self._collect_func_deps(term, func_decls)

                # Determine logic for this building block
                if not self._term_has_variables(term):
                    # Variable-free term: infer logic from operators
                    block_logic = self._infer_logic_from_term(term)
                else:
                    # Term contains variables: use file's logic
                    block_logic = logic

                # Create building block
                block = BuildingBlock(
                    term_smt2=str(term),
                    logic=block_logic,
                    sort_deps=sort_deps,
                    func_deps=func_deps,
                    var_decls=var_decls,
                    func_decls=func_decls,
                )
                blocks.append(block)

            except Exception as e:
                logger.warning("Failed to extract building block: %s", e)
                continue

        return blocks

    def _term_has_quantifier(self, term: Term) -> bool:
        """Check if a term contains quantifiers."""
        if term.quantifier is not None:
            return True
        if term.subterms:
            for s in term.subterms:
                if isinstance(s, Term) and self._term_has_quantifier(s):
                    return True
        return False

    def _term_has_variables(self, term: Term) -> bool:
        """Check if a term contains any variable references.

        Variables are terms with is_var=True, meaning they reference declared
        variables (not constants or operators).

        Note: Indexed literals like (_ bv1 8) or (_ +oo 8 24) may have is_var=True
        but are actually constants, not variables. We detect these by their name
        pattern starting with "(_ ".

        Similarly, rounding mode constants (RNE, RNA, RTZ, RTN, RTP) are built-in
        constants, not variables.
        """
        # Built-in rounding mode constants
        ROUNDING_MODES = frozenset({"RNE", "RNA", "RTZ", "RTN", "RTP"})

        def is_indexed_literal(t: Term) -> bool:
            """Check if term is an indexed literal (BV or FP constant)."""
            if t.name and t.name.startswith("(_ "):
                return True
            return False

        def is_builtin_constant(t: Term) -> bool:
            """Check if term is a built-in constant (rounding modes, etc.)."""
            if t.name and t.name in ROUNDING_MODES:
                return True
            return False

        if term.is_var:
            # Check if this is actually an indexed literal or built-in constant
            if is_indexed_literal(term) or is_builtin_constant(term):
                return False
            return True
        if term.subterms:
            for s in term.subterms:
                if isinstance(s, Term) and self._term_has_variables(s):
                    return True
        # Check quantified variables as well
        # quantified_vars can be: {} (empty dict), tuple of two lists, or None
        if term.quantifier is not None:
            # This is a quantifier term - it binds variables
            # The quantified variables are bound but count as variables
            if term.quantified_vars:
                if isinstance(term.quantified_vars, tuple) and len(term.quantified_vars) >= 1:
                    qvars = term.quantified_vars[0]
                    if qvars:
                        return True
        return False

    def _infer_logic_from_term(self, term: Term) -> str:
        """Infer the minimal logic required for a term based on operators used.

        This is used for variable-free terms to determine their actual logic
        requirements, rather than inheriting the file's logic classification.

        Analysis order (most specific first):
        1. String operators -> QF_S
        2. Bitvector operators -> QF_BV
        3. Floating-point operators -> QF_FP
        4. Array operators -> QF_AUFLIA (or simpler)
        5. Integer arithmetic -> QF_LIA or QF_NIA
        6. Real arithmetic -> QF_LRA or QF_NRA
        7. Core/Boolean only -> QF_UF
        8. Unclear/ambiguous -> "general"
        """
        from chimera.core.types import (
            CORE_OPS, NUMERICAL_OPS, INT_OPS, REAL_OPS,
            STRING_OPS, ARRAY_OPS, BV_OPS, FP_OPS,
        )

        term_str = str(term)

        # Collect all operators used in the term
        operators: Set[str] = set()
        has_nonlinear = False

        # Track types found by inspecting subterm.type and subterm.name
        has_int_type = False    # From explicit Int type
        has_real_type = False   # From explicit Real type
        has_bv_type = False     # From BitVec type
        has_fp_type = False     # From FloatingPoint type
        has_string_type = False  # From String type
        has_array_type = False  # From Array type
        has_unknown_type = False  # Unknown type (could be FP literal)

        def collect_info(t: Term) -> None:
            """Collect operators and type information from term tree."""
            nonlocal has_nonlinear
            nonlocal has_int_type, has_real_type, has_bv_type, has_fp_type
            nonlocal has_string_type, has_array_type, has_unknown_type

            # Collect operator
            if t.op is not None:
                if isinstance(t.op, str):
                    operators.add(t.op)
                    if t.op == "*":
                        has_nonlinear = True
                    # Check for FP operator prefix
                    if t.op.startswith("fp.") or t.op == "fp":
                        has_fp_type = True
                elif isinstance(t.op, Term):
                    op_str = str(t.op)
                    op_name = op_str.split(":")[0]
                    operators.add(op_name)
                    if op_name == "*":
                        has_nonlinear = True
                    if op_name.startswith("fp.") or op_name == "fp":
                        has_fp_type = True

            # Check type attribute
            if t.type:
                type_str = str(t.type)
                if "BitVec" in type_str:
                    has_bv_type = True
                elif "FloatingPoint" in type_str:
                    has_fp_type = True
                elif type_str == "Int":
                    has_int_type = True
                elif type_str == "Real":
                    has_real_type = True
                elif type_str == "String":
                    has_string_type = True
                elif type_str == "Bool":
                    pass  # Boolean is core, doesn't affect logic
                elif type_str == "Unknown":
                    has_unknown_type = True
                elif "Array" in type_str:
                    has_array_type = True

            # Check name attribute for indexed literals
            # BV literals: (_ bvN width) like (_ bv1 8), (_ bv255 32)
            # FP literals: (_ +oo eb sb), (_ NaN eb sb), (_ +zero eb sb)
            if t.name:
                name = t.name
                # Bit-vector indexed literals: (_ bv<digits> <width>)
                if name.startswith("(_ bv") or "(_ BitVec" in name:
                    has_bv_type = True
                # FP indexed literals: (_ +oo ...), (_ -oo ...), (_ NaN ...), (_ +zero ...), (_ -zero ...)
                elif name.startswith("(_ +oo") or name.startswith("(_ -oo"):
                    has_fp_type = True
                elif name.startswith("(_ NaN") or name.startswith("(_ +zero") or name.startswith("(_ -zero"):
                    has_fp_type = True
                # FP infinity/zero names without underscore prefix
                elif name in ("+oo", "-oo", "NaN", "+zero", "-zero"):
                    has_fp_type = True

            # Recurse into subterms
            if t.subterms:
                for s in t.subterms:
                    if isinstance(s, Term):
                        collect_info(s)

        collect_info(term)

        # Also check operators for BV/FP/String/Array
        has_bv_ops = any(op in operators for op in BV_OPS)
        has_fp_ops = any(op in operators for op in FP_OPS)
        has_string_ops = any(op in operators for op in STRING_OPS)
        has_array_ops = any(op in operators for op in ARRAY_OPS)
        has_int_ops = any(op in operators for op in INT_OPS)
        has_real_ops = any(op in operators for op in REAL_OPS)
        has_arith_ops = any(op in operators for op in NUMERICAL_OPS)

        # Combine type and operator information
        has_strings = has_string_type or has_string_ops
        has_bv = has_bv_type or has_bv_ops
        has_fp = has_fp_type or has_fp_ops
        has_arrays = has_array_type or has_array_ops
        has_int = has_int_type or has_int_ops
        has_real = has_real_type or has_real_ops

        # Detect Int/Real by looking for numeric literals in the term string
        # But be careful: (_ bv1 8) contains "1" and "8" but they're BV indices, not Int
        if not has_int and not has_real and not has_bv and not has_fp:
            import re
            # Check for integer literals (whole numbers not followed by .)
            # But exclude numbers in BV literal patterns like (_ bv1 8)
            # by checking the whole context
            if re.search(r'(?<!\.)\b\d+\b(?!\.)', term_str):
                # If this looks like a BV literal pattern, don't mark as Int
                if not re.search(r'\(_\s*bv\d+\s+\d+\)', term_str):
                    has_int = True
            # Check for real literals (numbers with decimal point)
            if re.search(r'\d+\.\d*', term_str) or re.search(r'\.\d+', term_str):
                has_real = True

        # Build logic name based on theories detected
        # Priority: Strings > BV > FP > Arrays > Arithmetic > Core

        if has_strings:
            return "QF_S"

        # Pure bitvector (no mixing with arithmetic or FP)
        if has_bv and not has_fp and not has_arrays and not has_int and not has_real:
            return "QF_BV"

        # Pure floating-point
        if has_fp and not has_bv and not has_arrays and not has_int and not has_real:
            return "QF_FP"

        if has_arrays:
            parts = ["QF", "A"]
            if has_int or has_real:
                parts.append("UFLIA" if has_int else "UFLRA")
            else:
                parts.append("UF")
            return "".join(parts)

        # Arithmetic logics
        if has_int and has_real:
            if has_nonlinear:
                return "QF_NIRA"
            return "QF_LIRA"
        elif has_int:
            if has_nonlinear:
                return "QF_NIA"
            return "QF_LIA"
        elif has_real:
            if has_nonlinear:
                return "QF_NRA"
            return "QF_LRA"

        # Check for arithmetic operators even without explicit types
        if has_int_ops:
            if has_nonlinear:
                return "QF_NIA"
            return "QF_LIA"
        if has_real_ops:
            if has_nonlinear:
                return "QF_NRA"
            return "QF_LRA"
        if has_arith_ops:
            return "QF_LIA"

        # Only core Boolean operators (and, or, not, =>, true, false, =, distinct, ite)
        if operators <= set(CORE_OPS) or not (operators - set(CORE_OPS)):
            return "QF_UF"

        # Has unknown types or operators we can't classify -> use "general"
        if has_unknown_type or (operators and not (operators <= set(CORE_OPS))):
            return "general"

        # Default: use UF as fallback
        return "QF_UF"

    def _collect_sort_deps(self, term: Term) -> Set[str]:
        """Collect all non-built-in sort dependencies from a term."""
        from chimera.core.logic_analyzer import is_builtin_sort

        sort_deps: Set[str] = set()

        def walk(t: Term) -> None:
            if t.type:
                type_str = str(t.type)
                if not is_builtin_sort(type_str):
                    sort_deps.add(type_str)

            if t.subterms:
                for s in t.subterms:
                    if isinstance(s, Term):
                        walk(s)

        walk(term)
        return sort_deps

    def _collect_func_deps(
        self,
        term: Term,
        known_funcs: Dict[str, FuncInfo],
    ) -> Set[str]:
        """Collect function names used in a term."""
        func_deps: Set[str] = set()

        def walk(t: Term) -> None:
            if t.op and isinstance(t.op, str) and t.op in known_funcs:
                func_deps.add(t.op)

            if t.subterms:
                for s in t.subterms:
                    if isinstance(s, Term):
                        walk(s)

        walk(term)
        return func_deps


def extract_corpus(
    input_dir: str,
    output_dir: str,
    logic_mapping: Optional[Dict[str, List[str]]] = None,
) -> Corpus:
    """Convenience function to extract corpus from directory.

    Parameters
    ----------
    input_dir : str
        Directory containing .smt2 files (recursively searched).
    output_dir : str
        Directory to save corpus JSON files.
    logic_mapping : Dict[str, List[str]], optional
        Pre-computed logic-to-files mapping.

    Returns
    -------
    Corpus
        Extracted and saved corpus.
    """
    # Collect all .smt2 files
    smt_files = []
    for root, _dirs, files in os.walk(input_dir):
        for f in files:
            if f.endswith(".smt2"):
                smt_files.append(os.path.join(root, f))

    logger.info("Found %d .smt2 files in %s", len(smt_files), input_dir)

    # Extract
    extractor = LogicAwareExtractor(logic_mapping=logic_mapping)

    def progress(current: int, total: int, logic: str) -> None:
        if current % 100 == 0 or current == total:
            logger.info("Processed %d/%d files (current logic: %s)", current, total, logic)

    corpus = extractor.extract_all(smt_files, progress_callback=progress)

    # Save
    corpus.save(output_dir)
    logger.info("Corpus saved to %s", output_dir)
    logger.info("Statistics: %s", corpus.statistics())

    return corpus
