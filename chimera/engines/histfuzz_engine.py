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

import copy
import logging
import os
import random
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

from chimera.core.smt_ast import (
    Assert,
    CheckSat,
    DeclareConst,
    DeclareFun,
    Expr,
    Hole,
    HoleCollector,
    Script,
    SkeletonExtractor,
    SmtSort,
    Term,
    TermKind,
    Var,
    collect_all_basic_subformulas,
    is_hole,
)
from chimera.core.smt_parser import parse_file, parse_string
from chimera.core.solver_manager import SolverConfig
from chimera.core.differential_oracle import OracleConfig
from chimera.engines.base import FuzzingStrategy

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Building-block pool
# ---------------------------------------------------------------------------

class BuildingBlockPool:
    """Collection of atomic ``Term`` fragments grouped by sort.

    Each block is stored together with the variables it references so
    that variable renaming can be applied when inserting a block into a
    skeleton.
    """

    def __init__(self) -> None:
        # sort_str → list of (term, {var_name: sort})
        self._pool: Dict[str, List[Tuple[Term, Dict[str, SmtSort]]]] = {}
        self._all: List[Tuple[Term, Dict[str, SmtSort]]] = []

    # -- population ----------------------------------------------------------

    def add(self, term: Term, variables: Dict[str, SmtSort]) -> None:
        """Add a single building block."""
        sort_key = str(term.type) if term.type else "Bool"
        entry = (term.clone(), dict(variables))
        self._pool.setdefault(sort_key, []).append(entry)
        self._all.append(entry)

    def add_from_script(self, script: Script) -> None:
        """Extract all atomic sub-terms from *script* and add them."""
        basics = collect_all_basic_subformulas(script)
        # Build a variable→sort map from the script declarations
        var_map: Dict[str, SmtSort] = {}
        for cmd in script.commands:
            if isinstance(cmd, DeclareConst):
                var_map[cmd.symbol] = cmd.sort
            elif isinstance(cmd, DeclareFun) and cmd.input_sort == "":
                var_map[cmd.symbol] = cmd.output_sort
        for term, _idx in basics:
            self.add(term, var_map)

    def add_from_files(self, paths: Sequence[str | Path], *, max_seeds: int = 100) -> int:
        """Load building blocks from up to *max_seeds* ``.smt2`` files.

        Returns the number of successfully parsed files.
        """
        count = 0
        shuffled = list(paths)
        random.shuffle(shuffled)
        for p in shuffled[:max_seeds]:
            result = parse_file(str(p), silent=True)
            if result is None:
                continue
            script, _globs = result
            self.add_from_script(script)
            count += 1
        logger.info("Loaded building blocks from %d/%d seed files", count, len(paths))
        return count

    # -- retrieval -----------------------------------------------------------

    def sample(self, sort_hint: Optional[str] = None) -> Optional[Term]:
        """Return a random building block, optionally matching *sort_hint*.

        Returns ``None`` when no block matches the given sort (no fallback).
        """
        if sort_hint:
            candidates = self._pool.get(sort_hint, [])
            if not candidates:
                return None
        else:
            candidates = self._all
            if not candidates:
                return None
        term, _vars = random.choice(candidates)
        return term.clone()

    @property
    def total(self) -> int:
        return len(self._all)

    @property
    def sort_keys(self) -> Set[str]:
        return set(self._pool.keys())


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
        extractor = SkeletonExtractor(rename_quantified=rename_quantified)
        for cmd in script.commands:
            if not isinstance(cmd, Assert):
                continue
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

    def add_from_files(self, paths: Sequence[str | Path]) -> int:
        """Extract skeletons from a list of ``.smt2`` files."""
        total_added = 0
        for p in paths:
            result = parse_file(str(p), silent=True)
            if result is None:
                continue
            script, _globs = result
            total_added += self.add_from_script(script)
        logger.info("Loaded %d unique skeletons from %d files", total_added, len(paths))
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

def fill_holes(
    skeleton: Term,
    pool: BuildingBlockPool,
) -> Term:
    """Replace every ``HOLE`` in *skeleton* with a block from *pool*.

    Returns a new ``Term`` (the skeleton is not mutated).
    """
    filled = skeleton.clone()

    collector = HoleCollector()
    collector.visit(filled)

    for hole in collector.holes:
        sort_hint = str(hole.type) if hole.type else None
        replacement = pool.sample(sort_hint=sort_hint)
        if replacement is None:
            # If no matching block found, leave the hole as-is
            # (will likely fail parsing but is safe).
            continue
        hole._initialize(
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
            parent=hole.parent,
        )
        hole._link_parents()

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
    skeleton_files : list[str], optional
        Pre-exported skeleton files (one skeleton per line).
    resource_dir : str, optional
        Directory containing per-logic building-block ``.txt`` files and
        ``skeleton.smt2``.
    """

    @property
    def name(self) -> str:
        return "histfuzz"

    def __init__(
        self,
        solver1: SolverConfig,
        solver2: SolverConfig,
        *,
        seed_dir: str = "",
        skeleton_files: Optional[List[str]] = None,
        resource_dir: Optional[str] = None,
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
        self._pool = BuildingBlockPool()
        self._skeletons = SkeletonStore()

        # Load seeds for building blocks
        seed_paths = self._discover_smt_files(seed_dir) if seed_dir else []
        if seed_paths:
            self._pool.add_from_files(seed_paths)

        # Load skeletons
        if skeleton_files:
            for sf in skeleton_files:
                self._skeletons.add_from_skeleton_file(sf)
        elif resource_dir:
            default_skel = os.path.join(resource_dir, "skeleton.smt2")
            if os.path.isfile(default_skel):
                self._skeletons.add_from_skeleton_file(default_skel)
            quant_skel = os.path.join(resource_dir, "skeleton_quant.smt2")
            if os.path.isfile(quant_skel):
                self._skeletons.add_from_skeleton_file(quant_skel)

        # Also extract skeletons from seed files
        if seed_paths:
            self._skeletons.add_from_files(seed_paths[:200])

        logger.info(
            "HistFuzz initialised: %d skeletons, %d building blocks",
            self._skeletons.total,
            self._pool.total,
        )

    # -- generation ----------------------------------------------------------

    def generate(self) -> Optional[str]:
        """Produce a formula by filling random skeletons with building blocks."""
        if self._skeletons.total == 0 or self._pool.total == 0:
            logger.warning("HistFuzz: empty skeletons or pool")
            return None

        chosen = self._skeletons.sample(n=random.randint(1, self._num_asserts))

        # Collect all variable declarations needed
        declarations: List[str] = []
        asserts: List[str] = []

        for skel_assert in chosen:
            filled = fill_holes(skel_assert.term, self._pool)
            asserts.append(f"(assert {filled})")

            # Collect variable declarations from the filled term
            self._collect_declarations(filled, declarations)

        # Deduplicate declarations
        seen_decls: Set[str] = set()
        unique_decls: List[str] = []
        for d in declarations:
            if d not in seen_decls:
                seen_decls.add(d)
                unique_decls.append(d)

        parts = unique_decls + asserts + ["(check-sat)"]
        return "\n".join(parts)

    # -- helpers -------------------------------------------------------------

    def _collect_declarations(self, term: Term, decls: List[str]) -> None:
        """Walk *term* and emit ``declare-const`` for every variable found."""
        if isinstance(term, str):
            return
        if term.is_var and term.name and term.type:
            decl = f"(declare-const {term.name} {term.type})"
            decls.append(decl)
            return
        if term.subterms:
            for sub in term.subterms:
                if isinstance(sub, Term):
                    self._collect_declarations(sub, decls)
        if term.let_terms:
            for lt in term.let_terms:
                if isinstance(lt, Term):
                    self._collect_declarations(lt, decls)

    @staticmethod
    def _discover_smt_files(directory: str) -> List[str]:
        """Recursively find all ``.smt2`` files under *directory*."""
        result: List[str] = []
        for root, _dirs, files in os.walk(directory):
            for f in files:
                if f.endswith(".smt2"):
                    result.append(os.path.join(root, f))
        return result
