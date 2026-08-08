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
from typing import Dict, List, Optional, Sequence, Union

from chimera.core.smt_ast import Script
from chimera.core.solver_manager import (
    SolverConfig,
    SolverOutcome,
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
    skipped: int = 0
    exhausted: int = 0
    retriable_failures: int = 0
    misconfigurations: int = 0
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
            f"parse_fails={self.parse_failures}  skipped={self.skipped}  "
            f"exhausted={self.exhausted}  retriable={self.retriable_failures}  "
            f"misconfigured={self.misconfigurations}"
        )


# ---------------------------------------------------------------------------
# Generation outcomes
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GeneratedCase:
    """A generated formula plus the data needed to reproduce its origin."""

    text: str
    logic: Optional[str] = None
    provenance: Optional[str] = None
    rng_seed: Optional[int] = None


@dataclass(frozen=True)
class Skipped:
    """A normal, temporary generation miss."""

    reason: str


@dataclass(frozen=True)
class Exhausted:
    """The producer cannot yield further cases without new input."""

    reason: str


@dataclass(frozen=True)
class Misconfigured:
    """A startup or producer configuration error that must fail fast."""

    reason: str


@dataclass(frozen=True)
class RetriableFailure:
    """An unexpected producer failure that may succeed on a later attempt."""

    reason: str


GenerationOutcome = Union[
    GeneratedCase,
    Skipped,
    Exhausted,
    Misconfigured,
    RetriableFailure,
]


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
    def generate(self, max_retries: int = 1) -> Optional[str]:
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
        max_consecutive_failures: int = 50,
    ) -> None:
        self.solver1 = solver1
        self.solver2 = solver2
        self.output_dir = output_dir
        self.temp_dir = temp_dir
        self.timeout = timeout
        self.oracle_config = oracle_config or OracleConfig()
        self.max_consecutive_failures = max_consecutive_failures
        self.stats = FuzzStats()

        os.makedirs(self.output_dir, exist_ok=True)
        os.makedirs(self.temp_dir, exist_ok=True)

    def preflight(self) -> List[Misconfigured]:
        """Return configuration errors that must stop a campaign before it runs."""
        issues: List[Misconfigured] = []
        if self.timeout <= 0:
            issues.append(Misconfigured("solver timeout must be positive"))
        if self.max_consecutive_failures <= 0:
            issues.append(Misconfigured("max_consecutive_failures must be positive"))
        for solver in (self.solver1, self.solver2):
            if not os.path.isfile(solver.binary):
                issues.append(Misconfigured(f"solver binary does not exist: {solver.binary}"))
            elif not os.access(solver.binary, os.X_OK):
                issues.append(Misconfigured(f"solver binary is not executable: {solver.binary}"))
        for directory in (self.output_dir, self.temp_dir):
            if not os.access(directory, os.W_OK):
                issues.append(Misconfigured(f"directory is not writable: {directory}"))
        return issues

    def generate_case(self, max_retries: int = 1) -> GenerationOutcome:
        """Adapt the legacy ``generate`` API into explicit campaign outcomes.

        Strategies can override this method once they can distinguish an
        exhausted corpus from a temporary miss.  Existing strategies retain
        their public ``generate`` implementation during the migration.
        """
        try:
            # Keep compatibility with third-party strategies that implemented
            # the original zero-argument ``generate()`` contract.
            formula_text = self.generate()
        except Exception as exc:
            logger.debug("%s: generator failed", self.name, exc_info=True)
            return RetriableFailure(str(exc) or type(exc).__name__)
        if formula_text is None:
            return Skipped("producer returned no formula")
        return GeneratedCase(formula_text, provenance=self.name)

    # -- single iteration ----------------------------------------------------

    def run_iteration(self, iteration_id: int = 0) -> List[BugReport]:
        """Execute one generate → solve → compare cycle.

        Returns all bug reports found in this iteration (usually 0 or 1).
        """
        self.stats.iterations += 1

        generated = self.generate_case()
        if not isinstance(generated, GeneratedCase):
            if isinstance(generated, Skipped):
                self.stats.skipped += 1
            elif isinstance(generated, Exhausted):
                self.stats.exhausted += 1
            elif isinstance(generated, Misconfigured):
                self.stats.misconfigurations += 1
            else:
                self.stats.retriable_failures += 1
            logger.debug("%s: %s at iter %d", self.name, generated.reason, iteration_id)
            return []

        formula_text = generated.text

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

        logger.debug(
            "%s iter %d: %s → %s | %s → %s",
            self.name, iteration_id,
            self.solver1.name, res1.outcome.name,
            self.solver2.name, res2.outcome.name,
        )

        # Log solver output on parse errors or unexpected outcomes
        for res, solver_name in ((res1, self.solver1.name), (res2, self.solver2.name)):
            if res.outcome in (SolverOutcome.PARSE_ERROR, SolverOutcome.ERROR):
                logger.warning(
                    "%s %s outcome=%s stdout=%r stderr=%r",
                    solver_name, res.smt_path, res.outcome.name,
                    res.stdout.strip()[:500], res.stderr.strip()[:500],
                )

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
        consecutive_failures = 0
        while max_iterations is None or i < max_iterations:
            try:
                generated_before = self.stats.formulas_generated
                self.run_iteration(i)
                if self.stats.formulas_generated == generated_before:
                    consecutive_failures += 1
                else:
                    consecutive_failures = 0
            except KeyboardInterrupt:
                logger.info("Campaign interrupted by user at iteration %d", i)
                break
            except Exception:
                logger.exception("Unexpected error at iteration %d", i)
                consecutive_failures += 1

            if consecutive_failures >= self.max_consecutive_failures:
                self.stats.exhausted += 1
                logger.error(
                    "%s campaign stopped after %d consecutive generation failures",
                    self.name,
                    consecutive_failures,
                )
                break

            if i > 0 and i % 100 == 0:
                logger.info(self.stats.summary())
            i += 1

        logger.info("Campaign finished. %s", self.stats.summary())
        return self.stats
