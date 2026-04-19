"""
Unit tests for logic_analyzer module (chimera/core/logic_analyzer.py).

Tests cover:
- LogicCapability flag operations
- LogicInfo creation and querying
- parse_logic function
- is_logic_compatible function
- is_builtin_sort function
- extract_sorts_from_declaration function
"""

import pytest
from chimera.core.logic_analyzer import (
    LogicCapability,
    LogicInfo,
    parse_logic,
    is_logic_compatible,
    get_compatible_logics,
    is_builtin_sort,
    extract_sorts_from_declaration,
    BUILTIN_SORTS,
)


class TestLogicCapability:
    """Tests for LogicCapability flag enum."""

    def test_capability_flags_exist(self):
        """Test that all capability flags are defined."""
        assert LogicCapability.QUANTIFIER_FREE
        assert LogicCapability.QUANTIFIERS
        assert LogicCapability.BITVECTORS
        assert LogicCapability.FLOATING_POINT
        assert LogicCapability.ARRAYS
        assert LogicCapability.INTEGERS
        assert LogicCapability.REALS
        assert LogicCapability.NONLINEAR
        assert LogicCapability.DIFFERENCE_LOGIC
        assert LogicCapability.UNINTERPRETED_FUNCS
        assert LogicCapability.STRINGS
        assert LogicCapability.SEQUENCES

    def test_capability_combination(self):
        """Test that capabilities can be combined with bitwise OR."""
        caps = LogicCapability.QUANTIFIER_FREE | LogicCapability.INTEGERS
        assert LogicCapability.QUANTIFIER_FREE in caps or (caps & LogicCapability.QUANTIFIER_FREE)
        assert LogicCapability.INTEGERS in caps or (caps & LogicCapability.INTEGERS)

    def test_capability_check_with_bitwise_and(self):
        """Test checking capability with bitwise AND."""
        caps = LogicCapability.QUANTIFIER_FREE | LogicCapability.BITVECTORS

        # Check if capabilities are set
        assert bool(caps & LogicCapability.QUANTIFIER_FREE)
        assert bool(caps & LogicCapability.BITVECTORS)
        assert not bool(caps & LogicCapability.ARRAYS)


class TestLogicInfo:
    """Tests for LogicInfo dataclass."""

    def test_basic_logic_info(self):
        """Test basic logic info creation."""
        info = LogicInfo(
            name="QF_LIA",
            capabilities=LogicCapability.QUANTIFIER_FREE | LogicCapability.INTEGERS,
            is_quantifier_free=True,
            theories=frozenset(["Int"]),
        )
        assert info.name == "QF_LIA"
        assert info.is_quantifier_free is True
        assert "Int" in info.theories

    def test_supports_method(self):
        """Test the supports() method."""
        info = LogicInfo(
            name="QF_LIA",
            capabilities=LogicCapability.QUANTIFIER_FREE | LogicCapability.INTEGERS,
            is_quantifier_free=True,
            theories=frozenset(["Int"]),
        )
        assert info.supports(LogicCapability.QUANTIFIER_FREE)
        assert info.supports(LogicCapability.INTEGERS)
        assert not info.supports(LogicCapability.BITVECTORS)

    def test_str_representation(self):
        """Test string representation."""
        info = LogicInfo(
            name="QF_BV",
            capabilities=LogicCapability.QUANTIFIER_FREE | LogicCapability.BITVECTORS,
            is_quantifier_free=True,
            theories=frozenset(["BV"]),
        )
        assert str(info) == "QF_BV"


class TestParseLogic:
    """Tests for parse_logic function."""

    def test_parse_qf_lia(self):
        """Test parsing QF_LIA logic."""
        info = parse_logic("QF_LIA")
        assert info.name == "QF_LIA"
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.QUANTIFIER_FREE)
        assert info.supports(LogicCapability.INTEGERS)
        assert not info.supports(LogicCapability.QUANTIFIERS)

    def test_parse_lia(self):
        """Test parsing LIA logic (with quantifiers)."""
        info = parse_logic("LIA")
        assert info.name == "LIA"
        assert info.is_quantifier_free is False
        assert info.supports(LogicCapability.QUANTIFIERS)
        assert info.supports(LogicCapability.INTEGERS)

    def test_parse_qf_bv(self):
        """Test parsing QF_BV logic."""
        info = parse_logic("QF_BV")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.BITVECTORS)

    def test_parse_qf_abv(self):
        """Test parsing QF_ABV logic (arrays + bitvectors)."""
        info = parse_logic("QF_ABV")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.ARRAYS)
        assert info.supports(LogicCapability.BITVECTORS)

    def test_parse_qf_auflia(self):
        """Test parsing QF_AUFLIA logic."""
        info = parse_logic("QF_AUFLIA")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.ARRAYS)
        assert info.supports(LogicCapability.UNINTERPRETED_FUNCS)
        assert info.supports(LogicCapability.INTEGERS)

    def test_parse_qf_fp(self):
        """Test parsing QF_FP logic (floating-point)."""
        info = parse_logic("QF_FP")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.FLOATING_POINT)

    def test_parse_qf_nia(self):
        """Test parsing QF_NIA logic (nonlinear integers)."""
        info = parse_logic("QF_NIA")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.INTEGERS)
        assert info.supports(LogicCapability.NONLINEAR)

    def test_parse_qf_nra(self):
        """Test parsing QF_NRA logic (nonlinear reals)."""
        info = parse_logic("QF_NRA")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.REALS)
        assert info.supports(LogicCapability.NONLINEAR)

    def test_parse_qf_idl(self):
        """Test parsing QF_IDL logic (integer difference logic)."""
        info = parse_logic("QF_IDL")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.INTEGERS)
        assert info.supports(LogicCapability.DIFFERENCE_LOGIC)

    def test_parse_qf_rdl(self):
        """Test parsing QF_RDL logic (real difference logic)."""
        info = parse_logic("QF_RDL")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.REALS)
        assert info.supports(LogicCapability.DIFFERENCE_LOGIC)

    def test_parse_qf_s(self):
        """Test parsing QF_S logic (strings)."""
        info = parse_logic("QF_S")
        assert info.is_quantifier_free is True
        assert info.supports(LogicCapability.STRINGS)

    def test_parse_case_insensitive(self):
        """Test that parsing is case-insensitive for the logic name."""
        info1 = parse_logic("qf_lia")
        info2 = parse_logic("QF_LIA")
        info3 = parse_logic("Qf_Lia")

        assert info1.is_quantifier_free is True
        assert info2.is_quantifier_free is True
        assert info3.is_quantifier_free is True

    def test_parse_all_logic(self):
        """Test parsing ALL logic (universal logic)."""
        info = parse_logic("ALL")
        # ALL should allow quantifiers
        assert info.supports(LogicCapability.QUANTIFIERS)


class TestIsLogicCompatible:
    """Tests for is_logic_compatible function."""

    def test_same_logic_compatible(self):
        """Test that same logic is always compatible."""
        assert is_logic_compatible("QF_LIA", "QF_LIA")
        assert is_logic_compatible("QF_BV", "QF_BV")
        assert is_logic_compatible("LIA", "LIA")

    def test_qf_to_qf_compatible(self):
        """Test QF formulas can be used in QF contexts."""
        assert is_logic_compatible("QF_LIA", "QF_LIA")
        assert is_logic_compatible("QF_LIA", "QF_UFLIA")
        assert is_logic_compatible("QF_BV", "QF_ABV")

    def test_quantified_to_qf_incompatible(self):
        """Test quantified formulas cannot be used in QF contexts."""
        assert not is_logic_compatible("LIA", "QF_LIA")
        assert not is_logic_compatible("AUFLIA", "QF_AUFLIA")
        assert not is_logic_compatible("NIA", "QF_NIA")

    def test_qf_to_quantified_compatible(self):
        """Test QF formulas can be used in quantified contexts."""
        assert is_logic_compatible("QF_LIA", "LIA")
        assert is_logic_compatible("QF_BV", "BV")

    def test_bv_requires_bv_in_target(self):
        """Test BV formulas require BV in target."""
        assert not is_logic_compatible("QF_BV", "QF_LIA")
        assert not is_logic_compatible("QF_BV", "QF_UFLIA")
        assert is_logic_compatible("QF_BV", "QF_ABV")

    def test_array_requires_array_in_target(self):
        """Test Array formulas require Array in target."""
        assert not is_logic_compatible("QF_ALIA", "QF_LIA")
        assert is_logic_compatible("QF_ALIA", "QF_AUFLIA")
        assert is_logic_compatible("QF_ABV", "QF_ABV")

    def test_fp_requires_fp_in_target(self):
        """Test FP formulas require FP in target."""
        assert not is_logic_compatible("QF_FP", "QF_LIA")
        assert not is_logic_compatible("QF_FP", "QF_BV")

    def test_nonlinear_requires_nonlinear(self):
        """Test nonlinear requires nonlinear in target."""
        assert not is_logic_compatible("QF_NIA", "QF_LIA")
        assert not is_logic_compatible("QF_NRA", "QF_LRA")
        assert is_logic_compatible("QF_LIA", "QF_NIA")  # Linear is OK for nonlinear

    def test_uf_requires_uf_in_target(self):
        """Test UF formulas require UF in target."""
        assert not is_logic_compatible("QF_UF", "QF_LIA")
        assert is_logic_compatible("QF_UF", "QF_UFLIA")

    def test_string_requires_string_in_target(self):
        """Test String formulas require String in target."""
        assert not is_logic_compatible("QF_S", "QF_LIA")


class TestGetCompatibleLogics:
    """Tests for get_compatible_logics function."""

    def test_qf_lia_compatible_logics(self):
        """Test finding compatible logics for QF_LIA."""
        available = frozenset([
            "QF_LIA", "QF_LRA", "QF_BV", "LIA", "QF_NIA"
        ])
        compatible = get_compatible_logics("QF_LIA", available)
        assert "QF_LIA" in compatible
        assert "QF_NIA" in compatible  # Linear works in nonlinear
        assert "LIA" in compatible  # QF works in quantified
        assert "QF_BV" not in compatible  # No BV

    def test_lia_compatible_logics(self):
        """Test finding compatible logics for LIA (quantified)."""
        available = frozenset([
            "QF_LIA", "QF_LRA", "LIA", "AUFLIA"
        ])
        compatible = get_compatible_logics("LIA", available)
        assert "LIA" in compatible
        assert "AUFLIA" in compatible
        assert "QF_LIA" not in compatible  # Quantified not OK for QF

    def test_empty_available_logics(self):
        """Test with empty available logics set."""
        compatible = get_compatible_logics("QF_LIA", frozenset())
        assert len(compatible) == 0


class TestIsBuiltinSort:
    """Tests for is_builtin_sort function."""

    def test_builtin_sorts(self):
        """Test that standard sorts are recognized as built-in."""
        assert is_builtin_sort("Bool")
        assert is_builtin_sort("Int")
        assert is_builtin_sort("Real")
        assert is_builtin_sort("String")
        assert is_builtin_sort("Array")

    def test_indexed_bitvector(self):
        """Test indexed bitvector sorts."""
        assert is_builtin_sort("(_ BitVec 32)")
        assert is_builtin_sort("(_ BitVec 64)")
        assert is_builtin_sort("(_ BitVec 8)")

    def test_indexed_floating_point(self):
        """Test indexed floating-point sorts."""
        assert is_builtin_sort("(_ FloatingPoint 8 24)")
        assert is_builtin_sort("(_ Float16)")
        assert is_builtin_sort("(_ Float32)")
        assert is_builtin_sort("(_ Float64)")

    def test_parametric_array(self):
        """Test parametric array sorts."""
        assert is_builtin_sort("(Array Int Int)")
        assert is_builtin_sort("(Array (_ BitVec 32) Real)")

    def test_custom_sorts_not_builtin(self):
        """Test that custom sorts are not built-in."""
        assert not is_builtin_sort("MySort")
        assert not is_builtin_sort("CustomType")
        assert not is_builtin_sort("Person")
        assert not is_builtin_sort("State")


class TestExtractSortsFromDeclaration:
    """Tests for extract_sorts_from_declaration function."""

    def test_declare_fun_simple(self):
        """Test extracting sorts from simple declare-fun."""
        sorts = extract_sorts_from_declaration("(declare-fun x () Int)")
        # Int is builtin, should be empty
        assert "Int" not in sorts or len(sorts) == 0

    def test_declare_fun_with_args(self):
        """Test extracting sorts from declare-fun with arguments."""
        sorts = extract_sorts_from_declaration("(declare-fun f (Int Bool) Int)")
        # Int and Bool are builtin
        assert len(sorts) == 0 or all(is_builtin_sort(s) for s in sorts)

    def test_declare_fun_custom_sort(self):
        """Test extracting custom sort from declaration."""
        sorts = extract_sorts_from_declaration("(declare-fun p () Person)")
        assert "Person" in sorts

    def test_declare_const(self):
        """Test extracting sorts from declare-const."""
        sorts = extract_sorts_from_declaration("(declare-const x Real)")
        # Real is builtin
        assert len(sorts) == 0 or "Real" not in sorts

    def test_define_fun(self):
        """Test extracting sorts from define-fun."""
        sorts = extract_sorts_from_declaration("(define-fun f ((x Int)) Bool true)")
        # Int and Bool are builtin
        assert len(sorts) == 0 or all(is_builtin_sort(s) for s in sorts)

    def test_multiple_custom_sorts(self):
        """Test extracting multiple custom sorts."""
        sorts = extract_sorts_from_declaration("(declare-fun transform (Person State) Event)")
        assert "Person" in sorts
        assert "State" in sorts
        assert "Event" in sorts

    def test_array_sort_builtin(self):
        """Test that array sorts don't extract as custom."""
        sorts = extract_sorts_from_declaration("(declare-fun arr () (Array Int Int))")
        # Array, Int are builtin
        for s in sorts:
            assert is_builtin_sort(s)

    def test_invalid_declaration(self):
        """Test handling of invalid declaration string."""
        sorts = extract_sorts_from_declaration("not a declaration")
        assert len(sorts) == 0


class TestBuiltinSorts:
    """Tests for BUILTIN_SORTS constant."""

    def test_builtin_sorts_set_exists(self):
        """Test that BUILTIN_SORTS is defined."""
        assert BUILTIN_SORTS is not None
        assert isinstance(BUILTIN_SORTS, frozenset)

    def test_builtin_sorts_contains_standard(self):
        """Test that BUILTIN_SORTS contains standard sorts."""
        assert "Bool" in BUILTIN_SORTS
        assert "Int" in BUILTIN_SORTS
        assert "Real" in BUILTIN_SORTS
        assert "String" in BUILTIN_SORTS
        assert "Array" in BUILTIN_SORTS
        assert "BitVec" in BUILTIN_SORTS


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
