"""
Dynamic generator loader module.

This module dynamically loads generator functions based on the configuration
in generator_config.py, allowing seamless switching between original and new generators.
"""

import sys
import importlib.util
from pathlib import Path
from generator_config import USE_NEW_GENERATORS, NEW_GENERATORS_PATH, get_new_generator_info

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


def load_new_generator(generator_name, short_name=None):
    """
    Dynamically load a new generator function from the new generators directory.
    
    Args:
        generator_name: Name of the generator module (e.g., "fixedsizebitvectors")
        short_name: Short name for the function (e.g., "bv" for bitvectors)
    
    Returns:
        The generator function, or None if loading fails
    """
    try:
        module_path = Path(NEW_GENERATORS_PATH) / f"{generator_name}_generator.py"
        if not module_path.exists():
            print(f"Warning: New generator module not found: {module_path}")
            return None
        
        spec = importlib.util.spec_from_file_location(f"{generator_name}_generator", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        # Try different possible function names
        # New generators use short names in function names (e.g., generate_ints_formula_with_decls)
        possible_names = [
            f"generate_{generator_name}_formula_with_decls",  # Full name
            f"generate_{generator_name}_formula",
        ]
        
        # If short_name is provided, also try with short name
        if short_name:
            possible_names.insert(0, f"generate_{short_name}_formula_with_decls")
            possible_names.insert(1, f"generate_{short_name}_formula")
        
        # Generic fallbacks
        possible_names.extend([
            "generate_formula_with_decls",
            "generate_formula",
        ])
        
        for func_name in possible_names:
            if hasattr(module, func_name):
                print(f"Loaded new generator: {generator_name} -> {func_name}")
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
