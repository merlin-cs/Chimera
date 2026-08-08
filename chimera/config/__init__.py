"""
Configuration module for Chimera fuzzer.

This module provides:
- Generator loading and configuration
- Theory selection for solver compatibility

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import importlib
from typing import Any

from chimera.config.generator_config import (
    USE_NEW_GENERATORS,
    NEW_GENERATORS_PATH,
    GENERATOR_PROFILE,
    get_generator_version,
    get_new_generator_info,
    get_new_generator_name,
    expected_generator_filename,
    find_generator_module_path,
    new_generator_file_exists,
)
from chimera.config.theory_selection import (
    SolverTheoryProfile,
    DEFAULT_PROFILE,
    get_compatible_theories,
)

_LEGACY_GENERATOR_EXPORTS = frozenset(
    {
        "GeneratorFn",
        "load_new_generator",
        "get_generator_function",
        "validate_theory_coverage",
        "GENERATORS",
    }
)


def __getattr__(name: str) -> Any:
    """Lazily expose legacy loader imports during migration.

    Importing ``chimera.config`` must not execute every generator module.  The
    old symbols remain available only when a caller explicitly requests one.
    """
    if name in _LEGACY_GENERATOR_EXPORTS:
        module = importlib.import_module("chimera.config.generator_loader")
        return getattr(module, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

__all__ = [
    # generator_config
    "USE_NEW_GENERATORS",
    "NEW_GENERATORS_PATH",
    "GENERATOR_PROFILE",
    "get_generator_version",
    "get_new_generator_info",
    "get_new_generator_name",
    "expected_generator_filename",
    "find_generator_module_path",
    "new_generator_file_exists",
    # generator_loader
    "GeneratorFn",
    "load_new_generator",
    "get_generator_function",
    "validate_theory_coverage",
    "GENERATORS",
    # theory_selection
    "SolverTheoryProfile",
    "DEFAULT_PROFILE",
    "get_compatible_theories",
]
