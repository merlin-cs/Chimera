"""
Global constants used across Chimera.

Guidelines
----------
* Every constant is typed and immutable (``Final`` / ``frozenset``).
* No hard-coded absolute paths – use environment variables or ``Path`` helpers.
* Theory lists are frozen sets so they cannot be mutated at runtime.
"""

from __future__ import annotations

import os
from typing import Final, FrozenSet

# -- Timing & limits ---------------------------------------------------------

ALARM_TIME: Final[int] = 60
MAX_ITERATIONS: Final[int] = 10
SAMPLE_SIZE: Final[int] = 3
OPTIMIZATION_THRESHOLD: Final[int] = 3
STOP_THRESHOLD: Final[int] = 5
MAX_INDEX: Final[int] = 1000
DEFAULT_TIMEOUT: Final[int] = 10
DEFAULT_STANDALONE_ITERATIONS: Final[int] = 1000
CORRECTION_THRESHOLD: Final[int] = 0

# -- String defaults ---------------------------------------------------------

DEFAULT_INCREMENTAL: Final[str] = "incremental"
DEFAULT_THEORY: Final[str] = "all"
DEFAULT_ADD_OPTION: Final[str] = "default"
TEMP_DIRECTORY: Final[str] = "./temp/"

# Checker path read from environment so nothing is hard-coded.
CHECKER_PATH: Final[str] = os.environ.get("CHECKER_PATH", "")

# -- Theory sets (immutable) -------------------------------------------------

GENERAL_THEORIES: FrozenSet[str] = frozenset({
    "fp", "int", "real", "core", "strings", "bv", "array", "reals_ints",
})

Z3_THEORIES: FrozenSet[str] = frozenset({"z3_seq"})

CVC5_THEORIES: FrozenSet[str] = frozenset({
    "bag", "datatype", "ff", "seq", "set", "ho", "trans", "sep",
})

BITWUZLA_THEORIES: FrozenSet[str] = frozenset({"core", "fp", "bv", "array"})

# Backward-compatible aliases (deprecated – use the new names above)
GENERAL_THEORYS = list(GENERAL_THEORIES)
Z3_THEORYS = list(Z3_THEORIES)
CVC5_THEORYS = list(CVC5_THEORIES)
BITWUZLA_THEORYS = list(BITWUZLA_THEORIES)
