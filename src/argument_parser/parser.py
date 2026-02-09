"""
Command-line argument parsing for Chimera.

Uses a dataclass to hold parsed values (instead of a mutable dict),
making the contract between the CLI and the rest of the system explicit.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, asdict
from typing import Any, Dict, Optional


@dataclass
class ChimeraArgs:
    """Immutable container for parsed CLI arguments."""

    solverbin1: Optional[str] = None
    solverbin2: Optional[str] = None
    solver1: Optional[str] = None
    solver2: Optional[str] = None
    option: str = "default"
    bugs: Optional[str] = None
    processes: Optional[int] = None
    timeout: int = 10
    iterations: int = 10
    standalone: bool = False
    generator_path: Optional[str] = None
    temp: str = "./temp/"
    history: bool = False
    rewrite: bool = False
    bug_type: str = "common"
    mimetic: int = 0
    logic: Optional[str] = None
    debug: bool = False

    def to_dict(self) -> Dict[str, Any]:
        """Return a plain dictionary (backward-compatible with legacy code)."""
        return asdict(self)


def _build_parser() -> argparse.ArgumentParser:
    """Construct the ``ArgumentParser`` (no side-effects)."""
    parser = argparse.ArgumentParser(
        description="Chimera – grammar-based SMT solver fuzzer",
    )
    parser.add_argument("--bugs", help="directory of historical bug-triggers")
    parser.add_argument("--solverbin1", help="path to the first solver binary")
    parser.add_argument("--solver1", help="first solver name (e.g. z3, cvc5)")
    parser.add_argument("--solverbin2", help="path to the second solver binary")
    parser.add_argument("--solver2", help="second solver name (e.g. z3, cvc5)")
    parser.add_argument(
        "--option", type=str, choices=["default", "regular", "comprehensive"],
        default="default",
        help="solver option profile (default: %(default)s)",
    )
    parser.add_argument(
        "--processes", "-p", type=int, default=None,
        help="number of parallel processes (default: CPU count)",
    )
    parser.add_argument(
        "--timeout", "-t", type=int, default=10,
        help="solver timeout in seconds (default: %(default)s)",
    )
    parser.add_argument(
        "--iterations", "-i", type=int, default=10,
        help="mutation iterations per seed (default: %(default)s)",
    )
    parser.add_argument("--standalone", action="store_true", help="standalone generation mode")
    parser.add_argument("--generator_path", type=str, default=None, help="path to custom generators")
    parser.add_argument("--temp", type=str, default="./temp/", help="directory for temporary files")
    parser.add_argument("--history", action="store_true", help="run in history mode")
    parser.add_argument("--rewrite", action="store_true", help="run in rewrite mode")
    parser.add_argument(
        "--bug_type", type=str, choices=["common", "all"], default="common",
        help="bug category filter (default: %(default)s)",
    )
    parser.add_argument("--mimetic", type=int, default=0, help="mimetic mutation iterations")
    parser.add_argument("--logic", type=str, default=None, help="target SMT-LIB logic")
    parser.add_argument("--debug", action="store_true", help="enable verbose debug logging for diagnostics")
    return parser


def parse_args(argv=None) -> ChimeraArgs:
    """Parse *argv* (or ``sys.argv``) and return a :class:`ChimeraArgs`."""
    ns = _build_parser().parse_args(argv)
    return ChimeraArgs(
        solverbin1=ns.solverbin1,
        solverbin2=ns.solverbin2,
        solver1=ns.solver1,
        solver2=ns.solver2,
        option=ns.option or "default",
        bugs=ns.bugs,
        processes=ns.processes,
        timeout=ns.timeout,
        iterations=ns.iterations,
        standalone=ns.standalone,
        generator_path=ns.generator_path,
        temp=ns.temp,
        history=ns.history,
        rewrite=ns.rewrite,
        bug_type=ns.bug_type,
        mimetic=ns.mimetic,
        logic=ns.logic,
        debug=ns.debug,
    )


# ---------------------------------------------------------------------------
# Backward-compatibility shim for existing callers.
# New code should use ``parse_args()`` directly.
# ---------------------------------------------------------------------------

class MainArgumentParser:
    """Legacy adapter – delegates to :func:`parse_args`."""

    def __init__(self) -> None:
        self._args: Optional[ChimeraArgs] = None

    def parse_arguments(self, _parser: argparse.ArgumentParser) -> None:  # noqa: ARG002
        self._args = parse_args()

    def get_arguments(self) -> Dict[str, Any]:
        if self._args is None:
            raise RuntimeError("parse_arguments() must be called first")
        return self._args.to_dict()

