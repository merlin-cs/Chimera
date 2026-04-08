"""
Chimera – Production-grade SMT solver fuzzing framework.

Integrates three state-of-the-art fuzzing techniques:
  1. **HistFuzz**: Skeleton enumeration with historical bug-triggering inputs.
  2. **Once4All**: Skeleton-guided fuzzing with LLM-synthesized term generators.
  3. **Aries**: Rewrite-space exploration via mimetic mutation & equality saturation.

Quick start::

    python -m chimera.chimera_cli \\
        --mode histfuzz \\
        --solver1-bin /usr/bin/z3 \\
        --solver2-bin /usr/bin/cvc5 \\
        --seed-dir ./seeds

API Usage::

    from chimera.core import parse_file, parse_string, SolverConfig, run_solver
    from chimera.core.smt_ast import Script, Term, Assert, DeclareConst
"""

__version__ = "2.0.0"

# Re-export commonly used symbols for convenience
from chimera.core import (
    parse_file,
    parse_string,
    SolverConfig,
    SolverResult,
    run_solver,
    BugKind,
    BugReport,
    compare,
)

__all__ = [
    "parse_file",
    "parse_string",
    "SolverConfig",
    "SolverResult",
    "run_solver",
    "BugKind",
    "BugReport",
    "compare",
]
