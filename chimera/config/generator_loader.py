"""
Dynamic generator loader module.

This module dynamically loads generator functions based on the configuration
in generator_config.py, allowing seamless switching between original and new generators.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import importlib.util
import logging
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from chimera.config.generator_config import (
    USE_NEW_GENERATORS,
    NEW_GENERATORS_PATH,
    GENERATOR_PROFILE,
    get_new_generator_info,
    expected_generator_filename,
    find_generator_module_path,
)

logger = logging.getLogger(__name__)

# Type alias for generator functions
GeneratorFn = Callable[[], Tuple[str, str]]


def _candidate_function_names(module_base: str, short_name: Optional[str]) -> List[str]:
    """Return likely function names across different LLM generator templates.

    Many LLM generators follow either:
      generate_<module_base>_formula_with_decls
      generate_<short>_formula_with_decls
    but some omit '_with_decls' or use generic function names.
    """
    candidates: List[str] = []
    if short_name:
        candidates.extend(
            [
                f"generate_{short_name}_formula_with_decls",
                f"generate_{short_name}_formula",
            ]
        )
    candidates.extend(
        [
            f"generate_{module_base}_formula_with_decls",
            f"generate_{module_base}_formula",
            "generate_formula_with_decls",
            "generate_formula",
        ]
    )
    # De-dup while keeping order.
    seen = set()
    unique: List[str] = []
    for name in candidates:
        if name not in seen:
            seen.add(name)
            unique.append(name)
    return unique


def load_new_generator(generator_name: str, short_name: Optional[str] = None) -> Optional[Callable]:
    """
    Dynamically load a new generator function from the new generators directory.

    Args:
        generator_name: Name of the generator module (e.g., "fixedsizebitvectors")
        short_name: Short name for the function (e.g., "bv" for bitvectors)

    Returns:
        The generator function, or None if loading fails
    """
    try:
        module_path = find_generator_module_path(generator_name)
        if not module_path:
            logger.debug(
                "New generator module not found for profile '%s': %s_generator.py",
                GENERATOR_PROFILE,
                generator_name,
            )
            return None

        spec = importlib.util.spec_from_file_location(f"{generator_name}_generator", module_path)
        if spec is None or spec.loader is None:
            return None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        possible_names = _candidate_function_names(generator_name, short_name)
        for func_name in possible_names:
            if hasattr(module, func_name):
                func = getattr(module, func_name)
                if callable(func):
                    logger.debug(
                        "Loaded new generator (%s): %s -> %s",
                        GENERATOR_PROFILE,
                        generator_name,
                        func_name,
                    )
                    return func

        logger.debug("Could not find generator function in %s", module_path)
        logger.debug("  Tried: %s", possible_names)
        return None

    except Exception as e:
        logger.warning("Error loading new generator %s: %s", generator_name, e)
        return None


def get_generator_function(generator_type: str) -> Optional[Callable]:
    """
    Get the appropriate generator function based on the configuration.

    Args:
        generator_type: The generator type (e.g., "bv", "fp", "core")

    Returns:
        The generator function (either original or new)
    """
    module_name, short_name = get_new_generator_info(generator_type)
    new_func = load_new_generator(module_name, short_name)
    if new_func:
        return new_func
    else:
        logger.warning("No generator found for %s", generator_type)
        return None


def validate_theory_coverage(theory_keys: List[str]) -> Dict[str, str]:
    """Validate that each theory key resolves to a callable generator.

    Returns a dict mapping theory_key -> status string.
    Status values:
      - "ok:new": resolved from LLM directory
      - "ok:original": resolved from original implementation
      - "missing": no generator found
    """
    results: Dict[str, str] = {}
    for key in theory_keys:
        func = get_generator_function(key)
        if callable(func):
            results[key] = "ok:new"
        else:
            results[key] = "missing"
    return results


# Pre-load all generators for better performance
GENERATORS: Dict[str, Optional[Callable]] = {
    "bag": get_generator_function("bag"),
    "datatype": get_generator_function("datatype"),
    "ff": get_generator_function("ff"),
    "ho": get_generator_function("ho"),
    "seq": get_generator_function("seq"),
    "set": get_generator_function("set"),
    "trans": get_generator_function("trans"),
    "sep": get_generator_function("sep"),
    "core": get_generator_function("core"),
    "strings": get_generator_function("strings"),
    "cvc5strings": get_generator_function("cvc5strings"),
    "real": get_generator_function("real"),
    "int": get_generator_function("int"),
    "fp": get_generator_function("fp"),
    "bv": get_generator_function("bv"),
    "array": get_generator_function("array"),
    "z3_seq": get_generator_function("z3_seq"),
    "reals_ints": get_generator_function("reals_ints"),
}
