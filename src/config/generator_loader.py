"""
Dynamic generator loader module.

This module dynamically loads generator functions based on the configuration
in generator_config.py, allowing seamless switching between original and new generators.
"""

import sys
import importlib.util
from pathlib import Path
from typing import Callable, Dict, List, Optional

from src.config.generator_config import (
    USE_NEW_GENERATORS,
    NEW_GENERATORS_PATH,
    GENERATOR_PROFILE,
    get_new_generator_info,
    expected_generator_filename,
    find_generator_module_path,
    new_generator_file_exists,
)

# Import original generators
from src.generator.bag_generator import generate_bag_formula_with_decls as original_bag
from src.generator.datatype_generator import generate_smtlib_datatype_with_decls as original_datatype
from src.generator.ff_generator import generate_ff_formula_with_decls as original_ff
from src.generator.ho_generator import produce_smtlib_formula_with_decls as original_ho
from src.generator.seq_generator import generate_seq_formula_with_decls as original_seq
from src.generator.set_generator import produce_smt_formula_with_decls as original_set
from src.generator.tras_generator import generate_trans_formula as original_trans
from src.generator.core_generator import generate_core_formula_with_decls as original_core
from src.generator.strings_generator import generate_strings_formula_with_decls as original_strings
from src.generator.real_generator import generate_real_formula_with_decls as original_real
from src.generator.int_generator import generate_int_formula_with_decls as original_int
from src.generator.fp_generator import generate_fp_formula_with_decls as original_fp
from src.generator.bv_generator import generate_bv_formula_with_decls as original_bv
from src.generator.array_generator import generate_array_formula_with_decls as original_array
from src.generator.z3_seq_generator import generate_z3_seq_formula_with_decls as original_z3_seq
from src.generator.real_int_generator import generate_reals_ints_formula_with_decls as original_reals_ints


def _candidate_function_names(module_base: str, short_name: Optional[str]) -> List[str]:
    """Return likely function names across different LLM generator templates."""

    # Many LLM generators follow either:
    #   generate_<module_base>_formula_with_decls
    #   generate_<short>_formula_with_decls
    # but some omit '_with_decls' or use generic function names.
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
            print(f"Warning: New generator module not found for profile '{GENERATOR_PROFILE}': {generator_name}_generator.py")
            return None
        
        spec = importlib.util.spec_from_file_location(f"{generator_name}_generator", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        possible_names = _candidate_function_names(generator_name, short_name)
        for func_name in possible_names:
            if hasattr(module, func_name):
                # print(f"Loaded new generator ({GENERATOR_PROFILE}): {generator_name} -> {func_name}")
                return getattr(module, func_name)
        
        print(f"Warning: Could not find generator function in {module_path}")
        print(f"  Tried: {possible_names}")
        return None
    
    except Exception as e:
        print(f"Error loading new generator {generator_name}: {e}")
        import traceback
        traceback.print_exc()
        return None


def get_generator_function(generator_type):
    """
    Get the appropriate generator function based on the configuration.
    
    Args:
        generator_type: The generator type (e.g., "bv", "fp", "core")
    
    Returns:
        The generator function (either original or new)
    """
    if USE_NEW_GENERATORS:
        module_name, short_name = get_new_generator_info(generator_type)
        new_func = load_new_generator(module_name, short_name)
        if new_func:
            return new_func
        else:
            print(f"Falling back to original generator for {generator_type}")
    
    # Fallback to original generators
    original_generators = {
        "bag": original_bag,
        "datatype": original_datatype,
        "ff": original_ff,
        "ho": original_ho,
        "seq": original_seq,
        "set": original_set,
        "trans": original_trans,
        "core": original_core,
        "strings": original_strings,
        "real": original_real,
        "int": original_int,
        "fp": original_fp,
        "bv": original_bv,
        "array": original_array,
        "z3_seq": original_z3_seq,
        "reals_ints": original_reals_ints,
        # Note: "sep" (separation logic) and "cvc5strings" only exist in new generators
    }
    
    return original_generators.get(generator_type)


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
            # If we can see an LLM file and new generators are enabled, call it ok:new.
            if USE_NEW_GENERATORS:
                if new_generator_file_exists(key):
                    results[key] = "ok:new"
                else:
                    results[key] = "ok:original"
            else:
                results[key] = "ok:original"
        else:
            results[key] = "missing"
    return results


# Pre-load all generators for better performance
GENERATORS = {
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
