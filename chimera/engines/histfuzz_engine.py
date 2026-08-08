"""
HistFuzz engine — skeleton enumeration with historical bug-triggering seeds.

Algorithm Overview
------------------
1. Parse a collection of historical bug-triggering ``.smt2`` files.
2. Extract "skeletons" by replacing atomic sub-terms with ``HOLE``
   placeholders (via ``SkeletonExtractor``).
3. Collect "building blocks" — atomic ``Term``s extracted from the seeds.
4. For each fuzzing iteration:
   a. Pick a random skeleton.
   b. Collect the ``HOLE`` positions.
   c. Fill each hole with a type-compatible building block from the pool.
   d. Emit the resulting SMT-LIB string.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import hashlib
import json
import os
import random
import re
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple

from chimera.core.differential_oracle import OracleConfig
from chimera.core.formula_builder import FormulaValidator, build_smt_script
from chimera.core.smt_ast import (
    Assert,
    DeclareConst,
    DeclareFun,
    HoleCollector,
    Script,
    SkeletonExtractor,
    SmtSort,
    Term,
    collect_all_basic_subformulas,
)
from chimera.core.smt_parser import parse_file, parse_string
from chimera.core.solver_manager import SolverConfig
from chimera.engines.base import (
    GeneratedCase,
    FuzzingStrategy,
    GenerationOutcome,
    Misconfigured,
    Skipped,
)
from chimera.history.corpus import BuildingBlock, BuildingBlockPool, Corpus, Skeleton
from chimera.history.streaming import (
    CorpusIntegrityError,
    load_corpus,
    packaged_corpus_path,
)

logger = logging.getLogger(__name__)


_BOOL_SORT = "Bool"
_INT_SORT = "Int"
_REAL_SORT = "Real"
_UNKNOWN_SORT = "Unknown"

_BOOLEAN_OPS = {"not", "and", "or", "xor", "=>", "implies"}
_BOOLEAN_RESULT_OPS = _BOOLEAN_OPS | {"=", "distinct", "<", "<=", ">", ">="}
_ARITHMETIC_OPS = {"+", "-", "*", "/", "div", "mod", "abs"}
def _sort_key(sort: Optional[SmtSort]) -> Optional[str]:
    if sort is None:
        return None
    return str(sort)


def _is_unknown_sort(sort: Optional[SmtSort]) -> bool:
    return _sort_key(sort) in (None, "", _UNKNOWN_SORT)


def _op_name(op: object) -> str:
    if isinstance(op, Term):
        return op.name or str(op)
    return str(op)


def _force_unknown_sort(term: Term, sort: SmtSort) -> None:
    """Propagate an expected sort through unknown leaves in simple expressions."""
    if _is_unknown_sort(term.type):
        term.type = sort
    if term.is_var or term.is_const:
        return
    if term.subterms:
        for sub in term.subterms:
            if isinstance(sub, Term):
                _force_unknown_sort(sub, sort)


def _rename_term_symbols(term: Term, suffix: str) -> None:
    """Rename variable symbols inside a sampled block to avoid sort collisions."""
    rename_map: Dict[str, str] = {}

    def renamed(name: str) -> str:
        if name not in rename_map:
            if name.startswith("|") and name.endswith("|") and len(name) >= 2:
                rename_map[name] = f"{name[:-1]}_{suffix}|"
            else:
                rename_map[name] = f"{name}_{suffix}"
        return rename_map[name]

    def walk(node: Term) -> None:
        if node.quantified_vars and len(node.quantified_vars) >= 2:
            names, sorts = node.quantified_vars
            new_names = []
            for name in names:
                new_names.append(renamed(str(name)))
            node.quantified_vars = (new_names, sorts)

        if node.is_var and node.name:
            node.name = renamed(node.name)

        if node.subterms:
            for sub in node.subterms:
                if isinstance(sub, Term):
                    walk(sub)
        if node.let_terms:
            for sub in node.let_terms:
                if isinstance(sub, Term):
                    walk(sub)

    walk(term)


def _infer_term_types(term: Term, variables: Dict[str, SmtSort]) -> Optional[SmtSort]:
    """Infer enough SMT sorts for HistFuzz type-compatible hole filling.

    The ANTLR AST is mostly syntactic and often leaves expression types as
    ``Unknown``. HistFuzz needs a conservative sort tag to avoid filling Bool
    holes with Int fragments and vice versa.
    """
    if term.is_var and term.name in variables:
        term.type = variables[term.name]
        return term.type
    if term.is_const or term.is_var:
        return term.type

    if term.quantifier is not None:
        local_vars = dict(variables)
        if term.quantified_vars and len(term.quantified_vars) >= 2:
            names, sorts = term.quantified_vars
            for name, sort in zip(names, sorts):
                local_vars[name] = sort
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _infer_term_types(sub, local_vars)
                    _force_unknown_sort(sub, _BOOL_SORT)
        term.type = _BOOL_SORT
        return term.type

    child_sorts: List[Optional[SmtSort]] = []
    if term.subterms:
        for sub in term.subterms:
            if isinstance(sub, Term):
                child_sorts.append(_infer_term_types(sub, variables))

    if term.op is None:
        return term.type

    op = _op_name(term.op)

    if op in _BOOLEAN_OPS:
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _force_unknown_sort(sub, _BOOL_SORT)
        term.type = _BOOL_SORT
        return term.type

    if op in {"=", "distinct"}:
        known = [s for s in child_sorts if not _is_unknown_sort(s)]
        if known and term.subterms:
            expected = known[0]
            if expected is not None:
                for sub in term.subterms:
                    if isinstance(sub, Term):
                        _force_unknown_sort(sub, expected)
        term.type = _BOOL_SORT
        return term.type

    if op in {"<", "<=", ">", ">="}:
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _force_unknown_sort(sub, _INT_SORT)
        term.type = _BOOL_SORT
        return term.type

    if op in _ARITHMETIC_OPS:
        result_sort: SmtSort = (
            _REAL_SORT if any(_sort_key(s) == _REAL_SORT for s in child_sorts) else _INT_SORT
        )
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _force_unknown_sort(sub, result_sort)
        term.type = result_sort
        return term.type

    if op == "ite" and len(child_sorts) >= 3:
        if term.subterms and isinstance(term.subterms[0], Term):
            _force_unknown_sort(term.subterms[0], _BOOL_SORT)
        branch_sorts = [s for s in child_sorts[1:] if not _is_unknown_sort(s)]
        if branch_sorts:
            term.type = branch_sorts[0]
        return term.type

    if op == "store" and child_sorts:
        if not _is_unknown_sort(child_sorts[0]):
            term.type = child_sorts[0]
        return term.type

    if op == "str.len":
        if term.subterms and isinstance(term.subterms[0], Term):
            _force_unknown_sort(term.subterms[0], "String")
        term.type = _INT_SORT
        return term.type

    if op in {"str.contains", "str.prefixof", "str.suffixof"}:
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _force_unknown_sort(sub, "String")
        term.type = _BOOL_SORT
        return term.type

    if op == "str.++":
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    _force_unknown_sort(sub, "String")
        term.type = "String"
        return term.type

    if op == "str.substr" and term.subterms:
        if isinstance(term.subterms[0], Term):
            _force_unknown_sort(term.subterms[0], "String")
        for sub in term.subterms[1:]:
            if isinstance(sub, Term):
                _force_unknown_sort(sub, _INT_SORT)
        term.type = "String"
        return term.type

    if op == "str.indexof" and term.subterms:
        for sub in term.subterms[:2]:
            if isinstance(sub, Term):
                _force_unknown_sort(sub, "String")
        for sub in term.subterms[2:]:
            if isinstance(sub, Term):
                _force_unknown_sort(sub, _INT_SORT)
        term.type = _INT_SORT
        return term.type

    if op == "str.replace" and term.subterms:
        for sub in term.subterms:
            if isinstance(sub, Term):
                _force_unknown_sort(sub, "String")
        term.type = "String"
        return term.type

    # A parsed function symbol can carry a declaration signature in its type.
    if isinstance(term.op, Term) and not _is_unknown_sort(term.op.type):
        parts = str(term.op.type).split()
        if parts:
            term.type = parts[-1]

    return term.type


def _infer_script_types(script: Script) -> Dict[str, SmtSort]:
    variables: Dict[str, SmtSort] = {}
    for cmd in script.commands:
        if isinstance(cmd, DeclareConst):
            variables[cmd.symbol] = cmd.sort
        elif isinstance(cmd, DeclareFun) and cmd.input_sort == "":
            variables[cmd.symbol] = cmd.output_sort

    for cmd in script.commands:
        if isinstance(cmd, Assert):
            _infer_term_types(cmd.term, variables)
            _force_unknown_sort(cmd.term, _BOOL_SORT)

    return variables


# ---------------------------------------------------------------------------
# Skeleton store
# ---------------------------------------------------------------------------

class SkeletonStore:
    """Maintains a deduplicated collection of assertion skeletons.

    A skeleton is an ``Assert`` whose body has been processed by
    ``SkeletonExtractor`` — atomic sub-expressions are replaced with
    ``HOLE`` terms.
    """

    def __init__(self) -> None:
        self._skeletons: List[Assert] = []
        self._seen: Set[str] = set()

    def add_from_script(self, script: Script, *, rename_quantified: bool = True) -> int:
        """Extract and store skeletons from the assert commands in *script*.

        Returns the number of newly added skeletons.
        """
        added = 0
        _infer_script_types(script)
        extractor = SkeletonExtractor(rename_quantified=rename_quantified)
        for cmd in script.commands:
            if not isinstance(cmd, Assert):
                continue
            _force_unknown_sort(cmd.term, _BOOL_SORT)
            skeleton_term = extractor.transform(cmd.term)
            key = str(skeleton_term)
            # Skip let-bindings (complex to fill)
            if "let " in key:
                continue
            if key not in self._seen:
                self._seen.add(key)
                self._skeletons.append(Assert(skeleton_term))
                added += 1
        return added

    def add_from_files(self, paths: Sequence[str | Path], *, max_seeds: int = 100) -> int:
        """Extract skeletons from a list of ``.smt2`` files."""
        total_added = 0
        shuffled = list(paths)
        random.shuffle(shuffled)
        for p in shuffled[:max_seeds]:
            result = parse_file(str(p), timeout=5, silent=True)
            if result is None:
                continue
            script, _globs = result
            total_added += self.add_from_script(script)
        logger.info(
            "Loaded %d unique skeletons from %d/%d seed files",
            total_added,
            min(max_seeds, len(paths)),
            len(paths),
        )
        return total_added

    def add_from_skeleton_file(self, path: str | Path) -> int:
        """Load pre-exported skeletons (one per line, in assert form)."""
        added = 0
        p = Path(path)
        if not p.is_file():
            logger.warning("Skeleton file not found: %s", path)
            return 0
        with open(p, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                result = parse_string(line, silent=True, prepare=False)
                if result is None:
                    continue
                script, _ = result
                for cmd in script.commands:
                    if isinstance(cmd, Assert):
                        key = str(cmd.term)
                        if key not in self._seen:
                            self._seen.add(key)
                            self._skeletons.append(cmd)
                            added += 1
        logger.info("Loaded %d skeletons from %s", added, path)
        return added

    def sample(self, n: int = 1) -> List[Assert]:
        """Return *n* random skeletons (with replacement)."""
        if not self._skeletons:
            return []
        return [random.choice(self._skeletons) for _ in range(n)]

    @property
    def total(self) -> int:
        return len(self._skeletons)


# ---------------------------------------------------------------------------
# Hole filler — the core generation step
# ---------------------------------------------------------------------------

def fill_holes(skeleton: Term, pool: BuildingBlockPool) -> Term:
    """Replace every ``HOLE`` in *skeleton* with a block from *pool*.

    Returns a new ``Term`` (the skeleton is not mutated).
    """
    filled = skeleton.clone()

    collector = HoleCollector()
    collector.visit(filled)

    for hole in collector.holes:
        sort_hint = str(hole.type) if hole.type else None
        replacement = pool.sample(sort_hint=sort_hint)
        replacement_term = replacement.term_obj if isinstance(replacement, BuildingBlock) else None
        if replacement_term is None:
            # If no matching block found, leave the hole as-is
            # (will likely fail parsing but is safe).
            continue
        hole.replace_with(replacement_term.clone())

    return filled


# ---------------------------------------------------------------------------
# HistFuzz Strategy
# ---------------------------------------------------------------------------

class HistFuzzStrategy(FuzzingStrategy):
    """Skeleton-enumeration fuzzer powered by historical bug-triggering seeds.

    Parameters
    ----------
    solver1, solver2 : SolverConfig
        The two solvers for differential testing.
    seed_dir : str
        Directory containing historical bug-triggering ``.smt2`` files.
    skeleton_files : List[str], optional
        Pre-exported skeleton files (one skeleton per line).
    resource_dir : str, optional
        Directory containing per-logic building-block ``.txt`` files and
        ``skeleton.smt2``.
    logic : str, optional
        Target SMT-LIB logic for filtering (e.g., "QF_LIA", "AUFLIA").
        If provided, only compatible skeletons and building blocks are used.
    use_new_corpus : bool
        If True, use the new logic-aware corpus system from chimera.history.
        If False (default), use legacy loading for backward compatibility.
    """

    @property
    def name(self) -> str:
        return "histfuzz"

    def __init__(
        self,
        solver1: SolverConfig,
        solver2: SolverConfig,
        *,
        corpus_dir: Optional[str] = None,
        seed_dir: str = "",
        skeleton_files: Optional[List[str]] = None,
        resource_dir: Optional[str] = None,
        logic: Optional[str] = None,
        use_new_corpus: bool = False,
        output_dir: str = "./chimera_bugs",
        temp_dir: str = "./chimera_temp",
        timeout: float = 10.0,
        oracle_config: Optional[OracleConfig] = None,
        num_asserts: int = 3,
    ) -> None:
        super().__init__(
            solver1,
            solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
            timeout=timeout,
            oracle_config=oracle_config,
        )
        self._num_asserts = num_asserts
        self._logic_filter = logic.upper() if logic else None
        deprecated = {
            "--seed-dir": seed_dir,
            "--skeleton-files": skeleton_files,
            "--resource-dir": resource_dir,
        }
        used = [name for name, value in deprecated.items() if value]
        if use_new_corpus:
            used.append("--use-new-corpus")
        if used:
            raise ValueError(
                "HistFuzz now uses a versioned JSON corpus; remove "
                + ", ".join(used)
                + " and pass --corpus-dir (or run chimera corpus extract)"
            )

        self._corpus_dir = Path(corpus_dir) if corpus_dir else packaged_corpus_path()
        self._corpus: Optional[Corpus] = None
        self._corpus_error: Optional[str] = None
        if self._corpus_dir.is_dir():
            try:
                self._corpus = load_corpus(self._corpus_dir)
            except (OSError, ValueError, CorpusIntegrityError) as exc:
                self._corpus_error = str(exc)
        logger.info(
            "HistFuzz initialised from JSON corpus %s (%s)",
            self._corpus_dir,
            self._corpus.statistics() if self._corpus else "unavailable",
        )

    def preflight(self) -> List[Misconfigured]:
        """Require a usable corpus before starting an unlimited campaign."""
        issues = super().preflight()
        if self._corpus_error:
            issues.append(Misconfigured(f"invalid HistFuzz corpus: {self._corpus_error}"))
        if not self._corpus or not self._corpus.skeletons or not self._corpus.blocks:
            issues.append(
                Misconfigured(
                    f"HistFuzz needs a non-empty JSON corpus at {self._corpus_dir}"
                )
            )
        return issues

    # -- generation ----------------------------------------------------------

    def generate(self, max_retries: int = 10) -> Optional[str]:
        """Produce a formula by filling random skeletons with building blocks.

        If logic filtering is enabled, only uses skeletons and building blocks
        compatible with the target logic. Validates generated formulas before
        returning.
        """
        if self._corpus:
            for _ in range(max(1, max_retries)):
                generated = self._generate_with_corpus()
                if generated is not None:
                    return generated
        return None

    def _generate_case_for_campaign(self, seed: int) -> GenerationOutcome:
        """Generate a case with stable corpus provenance for campaign artifacts."""
        for attempt in range(max(1, 10)):
            provenance = {
                "engine": self.name,
                "corpus": str(self._corpus_dir),
                "attempt": attempt,
                "rng_seed": seed,
                "skeleton": None,
                "blocks": [],
            }
            generated = self._generate_with_corpus(provenance)
            if generated is not None:
                return GeneratedCase(
                    generated,
                    logic=self._logic_filter,
                    provenance=provenance,
                    rng_seed=seed,
                )
        return Skipped("no valid formula could be generated from the HistFuzz corpus")

    @staticmethod
    def _corpus_record_id(record: object) -> str:
        """Return a deterministic identifier for a corpus record."""
        to_dict = getattr(record, "to_dict", None)
        payload = to_dict() if callable(to_dict) else str(record)
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()[:24]

    def _generate_with_corpus(self, provenance: dict[str, object] | None = None) -> Optional[str]:
        """Generate formula using the new logic-aware corpus."""

        corpus = self._corpus
        if corpus is None or not corpus.skeletons:
            logger.warning("HistFuzz (new corpus): empty corpus")
            return None

        # Determine compatible logics
        target_logic: Optional[str] = None
        if self._logic_filter:
            compatible_logics = corpus.get_compatible_logics(self._logic_filter)
            if not compatible_logics:
                logger.warning(
                    "HistFuzz: no compatible logics found for %s",
                    self._logic_filter,
                )
                return None
            # Use the user's target logic; sample_* will fall back to compatible
            # logics if no exact match exists (e.g., QF_SLIA → QF_S + QF_LIA blocks)
            target_logic = self._logic_filter
        else:
            available_logics = sorted(corpus.skeletons.keys())
            target_logic = random.choice(available_logics) if available_logics else None

        # Sample skeleton
        skeleton = corpus.sample_skeleton(
            logic=target_logic,
            quantified=False if self._logic_filter and self._logic_filter.startswith("QF") else None,
        )
        if skeleton is None:
            logger.warning("HistFuzz: no skeleton found for logic %s", target_logic)
            return None

        if provenance is not None:
            provenance["skeleton"] = {
                "id": self._corpus_record_id(skeleton),
                "logic": skeleton.logic,
                "quantified": skeleton.is_quantified,
            }

        # Fill holes with logic-aware block selection
        filled = self._fill_holes_with_corpus(skeleton, provenance)
        if filled is None:
            return None
        filled_term, sampled_blocks = filled

        # A parsed replacement term intentionally does not retain declaration
        # commands.  Carry both skeleton and block metadata into the rebuilt
        # script instead of trying to infer declarations from Unknown leaves.
        script = self._build_script_from_filled(
            filled_term,
            skeleton.var_decls,
            skeleton.func_decls,
            sampled_blocks,
        )

        # Validate
        result = FormulaValidator.validate(script, target_logic=self._logic_filter)
        if not result.ok:
            logger.debug(
                "HistFuzz: validation failed: %s",
                ", ".join(result.errors[:3]),
            )
            return None  # Will regenerate on next call

        return script

    def _fill_holes_with_corpus(
        self,
        skeleton: Skeleton,
        provenance: dict[str, object] | None = None,
    ) -> Optional[Tuple[Term, List[BuildingBlock]]]:
        """Fill skeleton holes using corpus blocks with type matching."""
        from chimera.core.smt_ast import HoleCollector

        corpus = self._corpus
        if corpus is None or not skeleton.term_obj:
            return None

        filled = skeleton.term_obj.clone()
        sampled_blocks: List[BuildingBlock] = []
        collector = HoleCollector()
        collector.visit(filled)

        for hole in collector.holes:
            sort_hint = str(hole.type) if hole.type else "Bool"
            replacement = corpus.sample_block(
                sort_hint=sort_hint,
                logic=skeleton.logic if not self._logic_filter else self._logic_filter,
            )
            if replacement is None or replacement.term_obj is None:
                # Leave hole as-is (will fail validation)
                logger.debug(
                    "HistFuzz: no block found for hole type %s",
                    sort_hint,
                )
                continue

            repl_term = replacement.term_obj.clone()
            hole.replace_with(repl_term)
            sampled_blocks.append(replacement)
            if provenance is not None:
                blocks = provenance.setdefault("blocks", [])
                if isinstance(blocks, list):
                    blocks.append(
                        {
                            "id": self._corpus_record_id(replacement),
                            "logic": replacement.logic,
                            "sort": replacement.type_hint,
                        }
                    )

        return filled, sampled_blocks

    def _build_script_from_filled(
        self,
        filled_term: Term,
        var_decls: Dict[str, str],
        func_decls: Mapping[str, Any],
        sampled_blocks: Sequence[BuildingBlock] = (),
    ) -> str:
        """Build complete SMT-LIB script from filled term."""
        declarations: List[str] = []

        # Metadata is the source of truth for declarations.  It survives
        # standalone parsing (where leaves deliberately have Unknown types),
        # and supports both declare-const and zero-arity declare-fun records.
        all_var_decls: List[Mapping[str, str]] = [var_decls]
        all_func_decls: List[Mapping[str, Any]] = [func_decls]
        for block in sampled_blocks:
            all_var_decls.append(block.var_decls)
            all_func_decls.append(block.func_decls)
        for declaration_map in all_var_decls:
            for name, sort in declaration_map.items():
                declarations.append(f"(declare-const {name} {sort})")
        for declaration_map in all_func_decls:
            for name, info in declaration_map.items():
                args = getattr(info, "arg_sorts", None)
                ret = getattr(info, "ret_sort", None)
                declared_name = getattr(info, "name", name)
                if isinstance(info, Mapping):
                    args = info.get("arg_sorts", args)
                    ret = info.get("ret_sort", ret)
                    declared_name = info.get("name", declared_name)
                if args is None or not ret:
                    continue
                declarations.append(
                    f"(declare-fun {declared_name} ({' '.join(str(arg) for arg in args)}) {ret})"
                )

        # Collect variable declarations from the filled term
        self._collect_declarations(filled_term, declarations)

        # Deduplicate
        seen = set()
        unique_decls = []
        for d in declarations:
            if d not in seen:
                seen.add(d)
                unique_decls.append(d)

        asserts = [f"(assert {filled_term})"]

        script = build_smt_script(
            declarations=unique_decls,
            assertions=asserts,
            logic=self._logic_filter or "ALL",
        )

        # Sanitize: SkeletonExtractor renames quantifier variable types to
        # TYPE0, TYPE1, etc. Replace with Int to avoid parse errors.
        script = re.sub(r"\bTYPE\d+\b", "Int", script)

        return script

    # -- helpers -------------------------------------------------------------

    def _collect_declarations(
        self,
        term: Term,
        decls: List[str],
        bound: Optional[Set[str]] = None,
    ) -> None:
        """Walk *term* and emit ``declare-const`` for every variable found.

        Handles edge cases:
        - Variables without type info (inferred from name heuristics)
        - Non-standard sorts (mapped to ``Int``)
        - Quantifier-bound variables are NOT declared here
        """
        if isinstance(term, str):
            return
        bound = bound or set()

        # Check if this is a quantified term — bound vars are not declared
        if term.quantifier is not None:
            q_bound = set(bound)
            if term.quantified_vars and len(term.quantified_vars) >= 2:
                q_bound.update(str(name) for name in term.quantified_vars[0])
            # Skip bound variables; recurse into body
            if term.subterms:
                for sub in term.subterms:
                    if isinstance(sub, Term):
                        self._collect_declarations(sub, decls, q_bound)
            return

        # Collect let-bound variable names so we don't declare them
        let_bound: Set[str] = set()
        if term.var_binders:
            let_bound.update(str(name) for name in term.var_binders)
        if term.let_terms:
            for lt in term.let_terms:
                if isinstance(lt, Term):
                    self._collect_declarations(lt, decls, bound)
        scoped_bound = bound | let_bound

        if term.is_var and term.name:
            type_str = str(term.type) if term.type else None

            # Skip placeholder types
            if type_str and (type_str == "Unknown" or re.match(r"^TYPE\d+$", type_str)):
                pass  # fall through to skip
            # Skip let-bound variable names
            elif term.name in scoped_bound:
                pass
            elif type_str and type_str not in ("Unknown", None):
                # Known type — emit declaration
                # Map common non-standard sorts to Int as a safe default
                if not self._is_valid_sort(type_str):
                    type_str = "Int"
                decl = f"(declare-const {term.name} {type_str})"
                if decl not in decls:
                    decls.append(decl)
            # No type info — skip (variable may be bound by outer quantifier
            # or may need declaration; we can't safely guess)

        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    self._collect_declarations(sub, decls, scoped_bound)

    @staticmethod
    def _is_valid_sort(sort_str: str) -> bool:
        """Check if a sort string is a recognized SMT-LIB sort."""
        builtin = {
            "Int", "Real", "Bool", "String",
            # BitVec is parameterized but we accept the name
            "bitvector", "BitVec",
        }
        # Parametric sorts start with "(" or contain known prefixes
        if sort_str.startswith("("):
            return True  # Assume parametric sort is valid
        return sort_str in builtin

    @staticmethod
    def _declare_undeclared_vars(
        formula: str, existing_decls: List[str]
    ) -> str:
        """Find undeclared free variables in *formula* and add declarations.

        Scans the SMT-LIB string for symbols that appear as operands but are
        not declared and not bound by quantifiers/let. Declares missing ones
        as ``(declare-const NAME Int)``.
        """
        # Collect declared variable names from the actual declarations
        declared: Set[str] = set()
        for d in existing_decls:
            # "(declare-const NAME SORT)"
            m = re.match(r"\(declare-(?:const|fun)\s+(\S+)\s+", d)
            if m:
                declared.add(m.group(1))

        # Collect quantifier/let-bound variable names
        bound: Set[str] = set()
        # forall/exists bindings: ((VAR0 TYPE0) (VAR1 TYPE1))
        for m in re.finditer(r"\((?:forall|exists)\s+\(([^)]*)\)", formula):
            for v in re.finditer(r"\((\S+)\s+\S+\)", m.group(1)):
                bound.add(v.group(1))
        # let bindings: ((name value) ...)
        for m in re.finditer(r"\(let\s+\(\((\S+)\s+", formula):
            bound.add(m.group(1))

        # Known SMT-LIB keywords and built-in symbols to skip.
        # Include hyphen-split fragments so "declare-const" doesn't produce
        # false matches for "declare" and "const".
        keywords: Set[str] = {
            "_",  # Reserved underscore
            "true", "false", "and", "or", "not", "xor",
            "distinct", "ite", "let", "forall", "exists", "assert",
            "check", "sat", "unsat", "unknown",
            "declare", "const", "fun", "define",
            "set", "logic", "push", "pop",
            "match", "as", "par",
            # String theory
            "str", "re",
            # Arithmetic
            "div", "mod", "abs",
            "to_real", "to_int", "is_int",
            # BitVec
            "bvand", "bvor", "bvxor", "bvnot", "bvneg",
            "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem",
            "bvult", "bvule", "bvugt", "bvuge",
            "bvslt", "bvsle", "bvsgt", "bvsge",
            "concat", "extract", "sign_extend", "zero_extend",
            "fp", "NaN", "inf",
            # Reserved SMT-LIB theory function symbols (shadowing prevention)
            "bv2nat", "nat2bv",
            "exp", "log", "sin", "cos", "tan", "asin", "acos", "atan",
            "arcsin", "arccos", "arctan",
            "sqrt", "pow",
            "store", "select",
            "member",
            "as", "par",
            # Hyphen-split keywords (full forms)
            "declare-fun", "declare-const", "define-fun", "set-logic",
            "check-sat", "get-model", "get-value", "get-assignment",
            "str.++", "str.len", "str.contains", "str.prefixof",
            "str.suffixof", "str.indexof", "str.replace", "str.replace_all",
            "str.replace_re", "str.replace_re_all",
            "str.substr", "str.at", "str.to_re", "str.in_re",
            "str.from_int", "str.to_int", "str.is_digit",
            "str.to_code", "str.from_code",
            "re.none", "re.all", "re.allchar", "re.++", "re.union",
            "re.inter", "re.*", "re.+", "re.opt", "re.range",
            "re.comp", "re.diff",
            # Sorts
            "Int", "Real", "Bool", "String", "RegL",
        }

        # Strip declaration/metadata lines, then scan only assert content.
        # This avoids matching fragments like "declare", "const" from
        # "(declare-const ...)" lines.
        content_lines = []
        for line in formula.split("\n"):
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith("(declare-"):
                continue
            if stripped.startswith("(set-logic"):
                continue
            if stripped.startswith("(push") or stripped.startswith("(pop"):
                continue
            content_lines.append(stripped)

        content = " ".join(content_lines)

        # Remove string literals to avoid matching symbols inside quotes
        content = re.sub(r'"[^"]*"', " ", content)

        # Remove sort annotations like (_ BitVec 32), (_ FloatingPoint 11 53)
        content = re.sub(r"\(_\s+\S+\s+\d+[^)]*\)", " ", content)

        # Find all identifier tokens in the remaining content
        symbols: Set[str] = set()
        pattern = r"\b([a-zA-Z_][a-zA-Z0-9_']*)\b"
        for m in re.finditer(pattern, content):
            sym = m.group(1)
            if sym not in keywords and sym not in declared and sym not in bound:
                # Skip pure numbers
                if re.match(r"^\d+$", sym):
                    continue
                symbols.add(sym)

        # Add declarations for missing symbols
        if symbols:
            extra_decls = []
            for sym in sorted(symbols):
                extra_decls.append(f"(declare-const {sym} Int)")
            # Insert after any existing declarations
            lines = formula.split("\n")
            insert_idx = 0
            for i, line in enumerate(lines):
                if line.startswith("(declare-"):
                    insert_idx = i + 1
            lines[insert_idx:insert_idx] = extra_decls
            formula = "\n".join(lines)

        return formula

    @staticmethod
    def _discover_smt_files(directory: str) -> List[str]:
        """Recursively find all ``.smt2`` files under *directory*."""
        result: List[str] = []
        for root, _dirs, files in os.walk(directory):
            for f in files:
                if f.endswith(".smt2"):
                    result.append(os.path.join(root, f))
        return result
