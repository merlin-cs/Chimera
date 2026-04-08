"""
Safe subprocess wrapper for executing SMT solvers.

Design Goals
------------
* **Strict timeouts** — never let a solver run longer than requested.
* **Zombie prevention** — always kill the entire process group on timeout.
* **Clean capture** — ``stdout`` and ``stderr`` are returned as strings.
* **Structured results** — every invocation returns a ``SolverResult``
  dataclass, never a bare string.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import os
import signal
import subprocess
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path
from typing import Final, List, Optional, Sequence

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Result types
# ---------------------------------------------------------------------------

class SolverOutcome(Enum):
    """Coarse classification of a solver run."""

    SAT = auto()
    UNSAT = auto()
    UNKNOWN = auto()
    TIMEOUT = auto()
    CRASH = auto()            # non-zero exit / signal
    SEGFAULT = auto()
    ASSERT_VIOLATION = auto()
    INVALID_MODEL = auto()
    PARSE_ERROR = auto()
    ERROR = auto()             # generic solver error

    @staticmethod
    def from_stdout(text: str) -> "SolverOutcome":
        """Classify a single-line solver answer."""
        stripped = text.strip()
        if stripped == "sat":
            return SolverOutcome.SAT
        if stripped == "unsat":
            return SolverOutcome.UNSAT
        if stripped == "unknown":
            return SolverOutcome.UNKNOWN
        return SolverOutcome.ERROR


@dataclass(frozen=True)
class SolverResult:
    """Immutable record of a single solver invocation."""

    outcome: SolverOutcome
    stdout: str = ""
    stderr: str = ""
    exit_code: Optional[int] = None
    wall_seconds: float = 0.0
    command: str = ""
    smt_path: str = ""

    @property
    def is_normal(self) -> bool:
        """``True`` when the solver terminated with a recognisable answer."""
        return self.outcome in (
            SolverOutcome.SAT,
            SolverOutcome.UNSAT,
            SolverOutcome.UNKNOWN,
        )

    @property
    def answer(self) -> Optional[str]:
        """Return ``'sat'``, ``'unsat'``, ``'unknown'``, or ``None``."""
        _MAP = {
            SolverOutcome.SAT: "sat",
            SolverOutcome.UNSAT: "unsat",
            SolverOutcome.UNKNOWN: "unknown",
        }
        return _MAP.get(self.outcome)


# ---------------------------------------------------------------------------
# Error-pattern classification (applied to combined output)
# ---------------------------------------------------------------------------

_ERROR_PATTERNS: Final[list[tuple[str, SolverOutcome]]] = [
    ("Segmentation fault", SolverOutcome.SEGFAULT),
    ("segmentation fault", SolverOutcome.SEGFAULT),
    ("SIGSEGV", SolverOutcome.SEGFAULT),
    ("NullPointerException", SolverOutcome.CRASH),
    ("ASSERTION VIOLATION", SolverOutcome.ASSERT_VIOLATION),
    ("AssertionError", SolverOutcome.ASSERT_VIOLATION),
    ("invalid model", SolverOutcome.INVALID_MODEL),
    ("ERRORS SATISFYING", SolverOutcome.INVALID_MODEL),
    ("model doesn't satisfy", SolverOutcome.INVALID_MODEL),
    ("Parse Error", SolverOutcome.PARSE_ERROR),
    ("unsupported reserved word", SolverOutcome.PARSE_ERROR),
    ("option parsing", SolverOutcome.ERROR),
]


def _classify_output(stdout: str, stderr: str) -> Optional[SolverOutcome]:
    """Scan solver output for known error patterns.

    Returns ``None`` when no pattern matches (i.e. output looks normal).
    """
    combined = stdout + "\n" + stderr
    for pattern, outcome in _ERROR_PATTERNS:
        if pattern in combined:
            return outcome
    return None


# ---------------------------------------------------------------------------
# Solver configuration
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SolverConfig:
    """Describes how to invoke a solver binary.

    Parameters
    ----------
    name : str
        Human-readable solver name (``z3``, ``cvc5``, ``bitwuzla``).
    binary : str | Path
        Absolute path to the solver executable.
    base_args : list[str]
        Arguments always passed (e.g. ``['-i']`` for incremental mode).
    extra_args : list[str]
        Optional arguments added per-run (random options, check-models, …).
    """

    name: str
    binary: str
    base_args: List[str] = field(default_factory=list)
    extra_args: List[str] = field(default_factory=list)

    def command(self, smt_path: str) -> List[str]:
        """Build the full command-line list."""
        return [
            self.binary,
            *self.base_args,
            *self.extra_args,
            smt_path,
        ]


# ---------------------------------------------------------------------------
# Default argument templates
# ---------------------------------------------------------------------------

def default_z3_args(
    *,
    timeout_ms: int = 10_000,
    incremental: bool = False,
    check_models: bool = True,
) -> List[str]:
    """Return standard Z3 CLI arguments."""
    args: List[str] = []
    if incremental:
        args.append("-in")
    if check_models:
        args.append("model_validate=true")
    args.append(f"-T:{timeout_ms // 1000}")
    return args


def default_cvc5_args(
    *,
    timeout_ms: int = 10_000,
    incremental: bool = False,
    check_models: bool = True,
) -> List[str]:
    """Return standard cvc5 CLI arguments."""
    args: List[str] = ["-q"]
    if incremental:
        args.append("-i")
    if check_models:
        args.append("--check-models")
    args.extend(["--strings-exp", f"--tlimit={timeout_ms}"])
    return args


# ---------------------------------------------------------------------------
# Core execution
# ---------------------------------------------------------------------------

def run_solver(
    config: SolverConfig,
    smt_path: str,
    *,
    timeout: float = 30.0,
) -> SolverResult:
    """Execute *config.binary* on *smt_path* with strict timeout.

    * A new process group is created so that ``os.killpg`` can reap the
      entire group on timeout (prevents zombies from forked children).
    * ``stdout`` and ``stderr`` are captured as UTF-8 strings.

    Returns
    -------
    SolverResult
        Fully populated result; callers never need to catch exceptions.
    """
    cmd = config.command(smt_path)
    cmd_str = " ".join(cmd)
    logger.debug("Running: %s", cmd_str)

    start = time.monotonic()

    try:
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            # Start a new process group so we can kill the whole tree.
            preexec_fn=os.setsid,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except FileNotFoundError:
        logger.error("Solver binary not found: %s", config.binary)
        return SolverResult(
            outcome=SolverOutcome.ERROR,
            stderr=f"Binary not found: {config.binary}",
            command=cmd_str,
            smt_path=smt_path,
        )
    except OSError as exc:
        logger.error("Failed to start solver: %s", exc)
        return SolverResult(
            outcome=SolverOutcome.ERROR,
            stderr=str(exc),
            command=cmd_str,
            smt_path=smt_path,
        )

    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        elapsed = time.monotonic() - start
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        # Kill the entire process group
        _kill_process_group(proc)
        elapsed = time.monotonic() - start
        logger.debug("Solver timed out after %.1fs: %s", elapsed, cmd_str)
        return SolverResult(
            outcome=SolverOutcome.TIMEOUT,
            wall_seconds=elapsed,
            command=cmd_str,
            smt_path=smt_path,
        )

    # --- Classify the result ------------------------------------------------

    # Check for signal-based termination (negative return code on Unix)
    if exit_code is not None and exit_code < 0:
        sig = -exit_code
        if sig == signal.SIGSEGV:
            outcome = SolverOutcome.SEGFAULT
        elif sig == signal.SIGABRT:
            outcome = SolverOutcome.ASSERT_VIOLATION
        else:
            outcome = SolverOutcome.CRASH
        return SolverResult(
            outcome=outcome,
            stdout=stdout,
            stderr=stderr,
            exit_code=exit_code,
            wall_seconds=elapsed,
            command=cmd_str,
            smt_path=smt_path,
        )

    # Check output text for known error patterns
    pattern_match = _classify_output(stdout, stderr)
    if pattern_match is not None:
        return SolverResult(
            outcome=pattern_match,
            stdout=stdout,
            stderr=stderr,
            exit_code=exit_code,
            wall_seconds=elapsed,
            command=cmd_str,
            smt_path=smt_path,
        )

    # Normal answer
    first_line = stdout.strip().split("\n", 1)[0].strip() if stdout else ""
    outcome = SolverOutcome.from_stdout(first_line)

    return SolverResult(
        outcome=outcome,
        stdout=stdout,
        stderr=stderr,
        exit_code=exit_code,
        wall_seconds=elapsed,
        command=cmd_str,
        smt_path=smt_path,
    )


# ---------------------------------------------------------------------------
# Incremental mode (multiple check-sat in one file)
# ---------------------------------------------------------------------------

def run_solver_incremental(
    config: SolverConfig,
    smt_path: str,
    *,
    timeout: float = 30.0,
) -> List[SolverResult]:
    """Run a solver in incremental mode, returning one result per ``check-sat``.

    The solver is invoked once; each ``sat``/``unsat``/``unknown`` line in
    the output corresponds to one ``check-sat`` in the input.
    """
    single = run_solver(config, smt_path, timeout=timeout)
    if not single.is_normal:
        return [single]

    results: List[SolverResult] = []
    for line in single.stdout.strip().splitlines():
        stripped = line.strip()
        if stripped in ("sat", "unsat", "unknown"):
            results.append(SolverResult(
                outcome=SolverOutcome.from_stdout(stripped),
                stdout=stripped,
                exit_code=single.exit_code,
                wall_seconds=single.wall_seconds,
                command=single.command,
                smt_path=smt_path,
            ))
    return results if results else [single]


# ---------------------------------------------------------------------------
# Process cleanup
# ---------------------------------------------------------------------------

def _kill_process_group(proc: subprocess.Popen) -> None:
    """Send SIGKILL to the entire process group, then reap."""
    try:
        pgid = os.getpgid(proc.pid)
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=2)
