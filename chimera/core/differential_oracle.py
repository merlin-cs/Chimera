"""
Differential test oracle for SMT solver fuzzing.

Compares the results of two solver runs and classifies discrepancies
into actionable bug categories.

Bug Categories
--------------
* **Soundness** — ``sat`` vs ``unsat`` mismatch (the most critical).
* **Crash** — segfault, assertion violation, or non-zero exit.
* **Invalid Model** — solver's own ``--check-models`` flag flagged an error.
* **Performance** — one solver times out while the other answers quickly
  (optional, off by default).

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import os
import shutil
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path
from typing import List, Optional, Sequence

from chimera.core.solver_manager import SolverOutcome, SolverResult

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Bug classification
# ---------------------------------------------------------------------------

class BugKind(Enum):
    """Enumeration of detectable bug categories."""

    SOUNDNESS = auto()       # sat vs unsat
    CRASH = auto()            # segfault / abort / non-zero exit
    INVALID_MODEL = auto()    # solver's model checker rejected the model
    ASSERT_VIOLATION = auto() # internal assertion failure
    PERFORMANCE = auto()      # one solver >> slower than the other
    NONE = auto()             # no bug detected


@dataclass(frozen=True)
class BugReport:
    """Immutable record describing a detected discrepancy."""

    kind: BugKind
    smt_path: str
    solver1_result: SolverResult
    solver2_result: SolverResult
    description: str = ""
    solver1_options: str = ""
    solver2_options: str = ""

    def summary(self) -> str:
        """Return a human-readable one-liner."""
        s1 = self.solver1_result
        s2 = self.solver2_result
        return (
            f"[{self.kind.name}] {self.smt_path}: "
            f"{s1.command} → {s1.outcome.name} | "
            f"{s2.command} → {s2.outcome.name}"
        )


# ---------------------------------------------------------------------------
# Oracle configuration
# ---------------------------------------------------------------------------

@dataclass
class OracleConfig:
    """Tunables for the differential oracle."""

    detect_crashes: bool = True
    detect_soundness: bool = True
    detect_invalid_models: bool = True
    detect_performance: bool = False
    performance_ratio: float = 10.0     # x-times slower = performance bug


# ---------------------------------------------------------------------------
# The Oracle itself
# ---------------------------------------------------------------------------

_CRASH_OUTCOMES = frozenset({
    SolverOutcome.CRASH,
    SolverOutcome.SEGFAULT,
    SolverOutcome.ASSERT_VIOLATION,
})

_IGNORABLE = frozenset({
    SolverOutcome.TIMEOUT,
    SolverOutcome.ERROR,
    SolverOutcome.PARSE_ERROR,
})


def compare(
    result1: SolverResult,
    result2: SolverResult,
    *,
    config: Optional[OracleConfig] = None,
) -> List[BugReport]:
    """Compare two solver results and return all detected bugs.

    Parameters
    ----------
    result1, result2 : SolverResult
        Outputs of two independent solver runs on the **same** formula.
    config : OracleConfig, optional
        Controls which bug categories are active.

    Returns
    -------
    list[BugReport]
        Empty when no bug is detected.
    """
    cfg = config or OracleConfig()
    smt_path = result1.smt_path or result2.smt_path
    bugs: List[BugReport] = []

    # -- Crash detection -----------------------------------------------------
    if cfg.detect_crashes:
        for res, label in ((result1, "solver1"), (result2, "solver2")):
            if res.outcome in _CRASH_OUTCOMES:
                kind = (
                    BugKind.ASSERT_VIOLATION
                    if res.outcome == SolverOutcome.ASSERT_VIOLATION
                    else BugKind.CRASH
                )
                bugs.append(BugReport(
                    kind=kind,
                    smt_path=smt_path,
                    solver1_result=result1,
                    solver2_result=result2,
                    description=f"{label} crashed: {res.outcome.name}",
                ))

    # -- Invalid-model detection ---------------------------------------------
    if cfg.detect_invalid_models:
        for res, label in ((result1, "solver1"), (result2, "solver2")):
            if res.outcome == SolverOutcome.INVALID_MODEL:
                bugs.append(BugReport(
                    kind=BugKind.INVALID_MODEL,
                    smt_path=smt_path,
                    solver1_result=result1,
                    solver2_result=result2,
                    description=f"{label} returned invalid model",
                ))

    # -- Soundness detection -------------------------------------------------
    if cfg.detect_soundness:
        a1, a2 = result1.answer, result2.answer
        if (
            a1 in ("sat", "unsat")
            and a2 in ("sat", "unsat")
            and a1 != a2
        ):
            bugs.append(BugReport(
                kind=BugKind.SOUNDNESS,
                smt_path=smt_path,
                solver1_result=result1,
                solver2_result=result2,
                description=f"Soundness bug: {a1} vs {a2}",
            ))

    # -- Performance detection -----------------------------------------------
    if cfg.detect_performance:
        t1, t2 = result1.wall_seconds, result2.wall_seconds
        if t1 > 0 and t2 > 0:
            ratio = max(t1, t2) / min(t1, t2)
            if ratio >= cfg.performance_ratio:
                slow = "solver1" if t1 > t2 else "solver2"
                bugs.append(BugReport(
                    kind=BugKind.PERFORMANCE,
                    smt_path=smt_path,
                    solver1_result=result1,
                    solver2_result=result2,
                    description=(
                        f"{slow} is {ratio:.1f}x slower "
                        f"({t1:.2f}s vs {t2:.2f}s)"
                    ),
                ))

    return bugs


# ---------------------------------------------------------------------------
# Bug persistence (write bug artefacts to disk)
# ---------------------------------------------------------------------------

def save_bug(
    bug: BugReport,
    output_dir: str | Path,
) -> Path:
    """Save a bug report (SMT file + log) into a numbered sub-directory.

    Returns the path to the created directory.
    """
    base = Path(output_dir) / bug.kind.name.lower()
    base.mkdir(parents=True, exist_ok=True)

    # Find the next available index
    existing = sorted(
        (int(p.name) for p in base.iterdir() if p.is_dir() and p.name.isdigit()),
        default=-1,
    )
    idx = (existing[-1] if existing else -1) + 1 if existing else 0
    bug_dir = base / str(idx)
    bug_dir.mkdir(parents=True, exist_ok=True)

    # Copy the triggering formula
    smt_src = Path(bug.smt_path)
    if smt_src.is_file():
        shutil.copy2(smt_src, bug_dir)

    # Write an error log
    log_path = bug_dir / "error_log.txt"
    with open(log_path, "w", encoding="utf-8") as fh:
        fh.write(f"Bug kind   : {bug.kind.name}\n")
        fh.write(f"Formula    : {bug.smt_path}\n")
        fh.write(f"Description: {bug.description}\n\n")
        fh.write(f"--- Solver 1 ---\n")
        fh.write(f"Command : {bug.solver1_result.command}\n")
        fh.write(f"Outcome : {bug.solver1_result.outcome.name}\n")
        fh.write(f"Exit    : {bug.solver1_result.exit_code}\n")
        fh.write(f"Time    : {bug.solver1_result.wall_seconds:.2f}s\n")
        fh.write(f"stdout  :\n{bug.solver1_result.stdout}\n")
        fh.write(f"stderr  :\n{bug.solver1_result.stderr}\n\n")
        fh.write(f"--- Solver 2 ---\n")
        fh.write(f"Command : {bug.solver2_result.command}\n")
        fh.write(f"Outcome : {bug.solver2_result.outcome.name}\n")
        fh.write(f"Exit    : {bug.solver2_result.exit_code}\n")
        fh.write(f"Time    : {bug.solver2_result.wall_seconds:.2f}s\n")
        fh.write(f"stdout  :\n{bug.solver2_result.stdout}\n")
        fh.write(f"stderr  :\n{bug.solver2_result.stderr}\n")

    logger.info("Saved bug %s → %s", bug.kind.name, bug_dir)
    return bug_dir
