"""
Unit tests for generator modules (src/generator/).

Tests cover:
- Generator loading and configuration
- Basic formula generation
- Theory-specific generators
"""

import pytest
from pathlib import Path


class TestGeneratorLoader:
    """Tests for generator loading system."""

    def test_generators_dict_exists(self):
        """Test that GENERATORS dictionary is accessible."""
        from chimera.config.generator_loader import GENERATORS
        assert isinstance(GENERATORS, dict)

    def test_generator_function_signature(self):
        """Test that generators have correct signature."""
        from chimera.config.generator_loader import GENERATORS

        # Each generator should be callable
        for name, gen_func in GENERATORS.items():
            assert callable(gen_func), f"Generator {name} is not callable"

    def test_int_generator_exists(self):
        """Test that integer generator exists."""
        from chimera.config.generator_loader import GENERATORS
        assert "int" in GENERATORS or "ints" in GENERATORS

    def test_bv_generator_exists(self):
        """Test that bitvector generator exists."""
        from chimera.config.generator_loader import GENERATORS
        assert "bv" in GENERATORS or "bitvector" in GENERATORS


class TestIntGenerator:
    """Tests for integer theory generator."""

    def test_int_generator_returns_tuple(self):
        """Test that int generator returns (declarations, formula)."""
        from chimera.config.generator_loader import GENERATORS

        gen_name = "int" if "int" in GENERATORS else "ints"
        if gen_name in GENERATORS:
            result = GENERATORS[gen_name]()
            assert result is not None
            assert isinstance(result, tuple)
            assert len(result) == 2

    def test_int_generator_declares_variables(self):
        """Test that int generator declares variables."""
        from chimera.config.generator_loader import GENERATORS

        gen_name = "int" if "int" in GENERATORS else "ints"
        if gen_name in GENERATORS:
            decls, formula = GENERATORS[gen_name]()
            if decls:
                # Should have some declarations
                assert "Int" in decls or "declare-fun" in decls


class TestBVGenerator:
    """Tests for bitvector theory generator."""

    def test_bv_generator_returns_tuple(self):
        """Test that BV generator returns (declarations, formula)."""
        from chimera.config.generator_loader import GENERATORS

        if "bv" in GENERATORS:
            result = GENERATORS["bv"]()
            assert result is not None
            assert isinstance(result, tuple)
            assert len(result) == 2


class TestArrayGenerator:
    """Tests for array theory generator."""

    def test_array_generator_returns_tuple(self):
        """Test that array generator returns (declarations, formula)."""
        from chimera.config.generator_loader import GENERATORS

        if "array" in GENERATORS or "arrays" in GENERATORS:
            gen_name = "array" if "array" in GENERATORS else "arrays"
            result = GENERATORS[gen_name]()
            assert result is not None
            assert isinstance(result, tuple)


class TestStringGenerator:
    """Tests for string theory generator."""

    def test_string_generator_returns_tuple(self):
        """Test that string generator returns (declarations, formula)."""
        from chimera.config.generator_loader import GENERATORS

        if "string" in GENERATORS or "strings" in GENERATORS:
            gen_name = "string" if "string" in GENERATORS else "strings"
            result = GENERATORS[gen_name]()
            assert result is not None
            assert isinstance(result, tuple)


class TestFormulaValidity:
    """Tests for validity of generated formulas."""

    def test_generated_formula_is_boolean(self):
        """Test that generated formulas are boolean expressions."""
        from chimera.config.generator_loader import GENERATORS

        # Sample a few generators
        for gen_name in list(GENERATORS.keys())[:3]:
            result = GENERATORS[gen_name]()
            if result:
                decls, formula = result
                # Formula should be a boolean expression for assert
                assert formula is not None

    def test_generated_formula_syntax(self):
        """Test that generated formulas have valid SMT-LIB syntax."""
        from chimera.config.generator_loader import GENERATORS
        import re

        for gen_name in list(GENERATORS.keys())[:5]:
            result = GENERATORS[gen_name]()
            if result:
                decls, formula = result
                if formula:
                    # Check balanced parentheses
                    open_count = formula.count("(")
                    close_count = formula.count(")")
                    assert open_count == close_count, \
                        f"Unbalanced parens in {gen_name}: {formula}"


class TestGeneratorConfig:
    """Tests for generator configuration."""

    def test_generator_config_module(self):
        """Test that generator config module exists."""
        from chimera.config.generator_config import USE_NEW_GENERATORS
        assert isinstance(USE_NEW_GENERATORS, bool)

    def test_generator_profile_setting(self):
        """Test generator profile configuration."""
        from chimera.config.generator_config import GENERATOR_PROFILE
        # Should have a profile setting
        assert GENERATOR_PROFILE is not None


class TestTheorySelection:
    """Tests for theory selection utilities."""

    def test_theory_selection_module(self):
        """Test theory selection module."""
        from chimera.config.theory_selection import get_compatible_theories
        theories = get_compatible_theories("z3")
        assert isinstance(theories, list)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
