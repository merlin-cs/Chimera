"""
Abstract base class for fuzzing strategies.

Every engine (HistFuzz, Once4All, Aries) inherits from ``FuzzingStrategy``
so the orchestrator can treat them uniformly.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import os
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence

from chimera.core.smt_ast import Script
from chimera.core.solver_manager import (
    SolverConfig,
    SolverResult,
    run_solver,
)
from chimera.core.differential_oracle import (
    BugReport,
    OracleConfig,
    compare,
    save_bug,
)

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Fuzzing statistics
# ---------------------------------------------------------------------------

@dataclass
class FuzzStats:
    """Mutable counters shared (or per-worker) during a fuzzing campaign."""

    iterations: int = 0
    formulas_generated: int = 0
    bugs_found: int = 0
    crashes: int = 0
    soundness_bugs: int = 0
    invalid_models: int = 0
    parse_failures: int = 0
    start_time: float = field(default_factory=time.monotonic)

    @property
    def elapsed(self) -> float:
        return time.monotonic() - self.start_time

    def summary(self) -> str:
        return (
            f"[Stats] elapsed={self.elapsed:.1f}s  "
            f"iters={self.iterations}  generated={self.formulas_generated}  "
            f"bugs={self.bugs_found}  crashes={self.crashes}  "
            f"soundness={self.soundness_bugs}  "
            f"invalid_models={self.invalid_models}  "
            f"parse_fails={self.parse_failures}"
        )


# ---------------------------------------------------------------------------
# Abstract strategy
# ---------------------------------------------------------------------------

class FuzzingStrategy(ABC):
    """Interface that every fuzzing engine must implement.

    Subclasses **must** override:
    * ``name`` — a short identifier (``histfuzz``, ``once4all``, ``aries``).
    * ``generate()`` — produce an SMT-LIB string for one fuzzing iteration.

    The base class provides:
    * ``run_iteration()`` — write → invoke solvers → compare → record.
    * ``run_campaign()`` — continuous loop calling ``run_iteration``.
    """

    # -- abstract interface --------------------------------------------------

    @property
    @abstractmethod
    def name(self) -> str:
        """Short, CLI-friendly name for this strategy."""
        ...

    @abstractmethod
    def generate(self) -> Optional[str]:
        """Produce a single SMT-LIB formula string.

        Returns ``None`` when the engine has nothing to generate (e.g.
        exhausted skeleton pool).
        """
        ...

    # -- configuration -------------------------------------------------------

    def __init__(
        self,
        solver1: SolverConfig,
        solver2: SolverConfig,
        *,
        output_dir: str = "./chimera_bugs",
        temp_dir: str = "./chimera_temp",
        timeout: float = 10.0,
        oracle_config: Optional[OracleConfig] = None,
    ) -> None:
        self.solver1 = solver1
        self.solver2 = solver2
        self.output_dir = output_dir
        self.temp_dir = temp_dir
        self.timeout = timeout
        self.oracle_config = oracle_config or OracleConfig()
        self.stats = FuzzStats()

        os.makedirs(self.output_dir, exist_ok=True)
        os.makedirs(self.temp_dir, exist_ok=True)

    # -- single iteration ----------------------------------------------------

    def run_iteration(self, iteration_id: int = 0) -> List[BugReport]:
        """Execute one generate → solve → compare cycle.

        Returns all bug reports found in this iteration (usually 0 or 1).
        """
        self.stats.iterations += 1

        formula_text = self.generate()
        if formula_text is None:
            logger.debug("%s: generator returned None at iter %d", self.name, iteration_id)
            self.stats.parse_failures += 1
            return []

        self.stats.formulas_generated += 1

        # Write the formula to a temp file
        smt_path = os.path.join(
            self.temp_dir, f"{self.name}_{os.getpid()}_{iteration_id}.smt2"
        )
        try:
            with open(smt_path, "w", encoding="utf-8") as fh:
                fh.write(formula_text)
        except OSError as exc:
            logger.error("Failed to write %s: %s", smt_path, exc)
            return []

        # Invoke both solvers
        res1 = run_solver(self.solver1, smt_path, timeout=self.timeout)
        res2 = run_solver(self.solver2, smt_path, timeout=self.timeout)

        # Compare results
        bugs = compare(res1, res2, config=self.oracle_config)

        # Record bugs
        for bug in bugs:
            self.stats.bugs_found += 1
            if bug.kind.name == "CRASH":
                self.stats.crashes += 1
            elif bug.kind.name == "SOUNDNESS":
                self.stats.soundness_bugs += 1
            elif bug.kind.name == "INVALID_MODEL":
                self.stats.invalid_models += 1
            save_bug(bug, self.output_dir)
            logger.warning("BUG FOUND: %s", bug.summary())

        # Clean up temp file (keep only on bugs)
        if not bugs and os.path.exists(smt_path):
            try:
                os.remove(smt_path)
            except OSError:
                pass

        return bugs

    # -- continuous campaign -------------------------------------------------

    def run_campaign(self, max_iterations: Optional[int] = None) -> FuzzStats:
        """Run the fuzzing loop for up to *max_iterations*.

        If *max_iterations* is ``None``, runs indefinitely until interrupted.
        Returns the final ``FuzzStats``.
        """
        logger.info(
            "Starting %s campaign (max_iters=%s, solvers=%s vs %s)",
            self.name,
            "unlimited" if max_iterations is None else max_iterations,
            self.solver1.name,
            self.solver2.name,
        )

        i = 0
        while max_iterations is None or i < max_iterations:
            try:
                self.run_iteration(i)
            except KeyboardInterrupt:
                logger.info("Campaign interrupted by user at iteration %d", i)
                break
            except Exception:
                logger.exception("Unexpected error at iteration %d", i)

            if i > 0 and i % 100 == 0:
                logger.info(self.stats.summary())
            i += 1

        logger.info("Campaign finished. %s", self.stats.summary())
        return self.stats
