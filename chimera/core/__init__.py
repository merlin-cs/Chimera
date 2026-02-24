"""Core modules shared across all fuzzing engines.

Submodules
----------
smt_ast
    Refactored AST with Visitor / Transformer patterns.
smt_parser
    Clean ANTLR facade for parsing SMT-LIB 2.6 files and strings.
solver_manager
    Safe subprocess wrapper for invoking SMT solvers.
differential_oracle
    Test oracle comparing solver outputs for bug detection.
"""

from chimera.core.smt_parser import parse_file, parse_string
from chimera.core.solver_manager import SolverConfig, SolverResult, run_solver
from chimera.core.differential_oracle import BugKind, BugReport, compare

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
