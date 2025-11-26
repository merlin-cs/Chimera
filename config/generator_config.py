"""
Generator configuration module.

This module provides a flexible way to switch between different generator implementations.
Set USE_NEW_GENERATORS to True to use the new Claude-generated generators,
or False to use the original generators.
"""

import os

# Configuration flag - set this to switch between generator versions
USE_NEW_GENERATORS = os.environ.get('USE_NEW_GENERATORS', 'false').lower() == 'true'

# Path to new generators (adjust this path as needed)
NEW_GENERATORS_PATH = "/home/smtagent/generator/generated-gemini"

def get_generator_version():
    """Returns the current generator version being used."""
    return "new (Claude)" if USE_NEW_GENERATORS else "original"

# Generator name mappings between original and new versions
# Format: "original_name": ("new_module_name", "function_short_name")
GENERATOR_NAME_MAP = {
    # Original name -> (New module name, Short name used in function)
    "array": ("arrayex", "arrayex"),
    "bag": ("bags", "bags"),
    "core": ("core", "core"),
    "datatype": ("datatypes", "datatypes"),
    "ff": ("finitefields", "finitefields"),
    "fp": ("floatingpoint", "floatingpoint"),
    "bv": ("fixedsizebitvectors", "fixedsizebitvectors"),
    "ho": ("hocore", "hocore"),
    "int": ("ints", "ints"),
    "real": ("reals", "reals"),
    "reals_ints": ("realsints", "realsints"),
    "seq": ("sequences", "sequences"),
    "set": ("setsandrelations", "setsandrelations"),
    "strings": ("strings", "strings"),
    "cvc5strings": ("cvc5strings", "cvc5strings"),  # CVC5-specific strings
    "trans": ("transcendentals", "transcendentals"),  # Transcendentals (newly added)
    "sep": ("separationlogic", "separationlogic"),    # Separation logic (newly added)
    "z3_seq": ("sequences", "sequences"),  # Z3 sequences map to the same as CVC5
}

def get_new_generator_info(original_name):
    """
    Get the new generator module name and function short name for a given original generator name.
    
    Args:
        original_name: The original generator name (e.g., "bv", "fp")
    
    Returns:
        Tuple of (module_name, short_name) or (original_name, original_name) if not found
    """
    return GENERATOR_NAME_MAP.get(original_name, (original_name, original_name))

def get_new_generator_name(original_name):
    """
    Get the new generator name for a given original generator name.
    
    Args:
        original_name: The original generator name (e.g., "bv", "fp")
    
    Returns:
        The corresponding new generator module name (e.g., "fixedsizebitvectors", "floatingpoint")
    """
    module_name, _ = get_new_generator_info(original_name)
    return module_name
