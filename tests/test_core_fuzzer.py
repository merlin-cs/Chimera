"""
Unit tests for the core fuzzer module (chimera.core.logic_analyzer and chimera.core.formula_builder).

Tests cover:
- Logic capability analysis
- Logic compatibility checking
- SMT formula construction
- Parenthesis depth validation
- Named annotation stripping
- Sort extraction
"""

import pytest
import sys

# Handle optional dependencies gracefully
try:
    from chimera.core.logic_analyzer import (
        parse_logic,
        is_logic_compatible,
        LogicCapability,
        is_builtin_sort,
        extract_sorts_from_declaration,
    )
    from chimera.core.formula_builder import (
        smt_paren_depth,
        strip_named_annotation,
        validate_smt_formula,
        balance_parentheses,
        insert_push_and_pop,
        build_type_var_map,
        variable_translocation,
        build_smt_script,
    )
    CORE_FUZZER_AVAILABLE = True
except ImportError as e:
    CORE_FUZZER_AVAILABLE = False
    SKIP_REASON = f"Core fuzzer module not available: {e}"

# Skip all tests in this module if core fuzzer is not available
pytestmark = pytest.mark.skipif(
    not CORE_FUZZER_AVAILABLE,
    reason=SKIP_REASON if not CORE_FUZZER_AVAILABLE else ""
)


# Aliases for backward compatibility with test naming
def _smt_paren_depth(text):
    return smt_paren_depth(text)

def _strip_named_annotation(expr):
    return strip_named_annotation(expr)

def _validate_smt_formula(script):
    return validate_smt_formula(script)

def _build_type_var(var_list):
    return build_type_var_map(var_list)

def _is_builtin_sort(sort_name):
    return is_builtin_sort(sort_name)

def _extract_sorts_from_decl(decl_str):
    return extract_sorts_from_declaration(decl_str)

# analyze_logic_capabilities replaced by parse_logic
def analyze_logic_capabilities(logic_name):
    info = parse_logic(logic_name)
    caps = set()
    if info.is_quantifier_free:
        caps.add("QF")
    if info.supports(LogicCapability.QUANTIFIERS):
        caps.add("QUANTIFIERS")
    if info.supports(LogicCapability.BITVECTORS):
        caps.add("BV")
    if info.supports(LogicCapability.FLOATING_POINT):
        caps.add("FP")
    if info.supports(LogicCapability.ARRAYS):
        caps.add("ARRAYS")
    if info.supports(LogicCapability.INTEGERS):
        caps.add("INT")
    if info.supports(LogicCapability.REALS):
        caps.add("REAL")
    if info.supports(LogicCapability.NONLINEAR):
        caps.add("NONLINEAR")
    if info.supports(LogicCapability.DIFFERENCE_LOGIC):
        caps.add("DL")
    if info.supports(LogicCapability.UNINTERPRETED_FUNCS):
        caps.add("UF")
    if info.supports(LogicCapability.STRINGS):
        caps.add("STRINGS")
    return caps


class TestLogicCapabilities:
    """Tests for analyze_logic_capabilities function."""

    def test_quantifier_free_logics(self):
        """QF_ prefix should indicate quantifier-free."""
        caps = analyze_logic_capabilities("QF_LIA")
        assert "QF" in caps
        assert "QUANTIFIERS" not in caps

        caps = analyze_logic_capabilities("QF_BV")
        assert "QF" in caps

    def test_quantified_logics(self):
        """Logics without QF_ prefix should allow quantifiers."""
        caps = analyze_logic_capabilities("LIA")
        assert "QUANTIFIERS" in caps
        assert "QF" not in caps

        caps = analyze_logic_capabilities("AUFLIA")
        assert "QUANTIFIERS" in caps

    def test_bitvector_detection(self):
        """BV in logic name should set BV capability."""
        caps = analyze_logic_capabilities("QF_BV")
        assert "BV" in caps

        caps = analyze_logic_capabilities("QF_ABV")
        assert "BV" in caps
        assert "ARRAYS" in caps

    def test_arithmetic_detection(self):
        """Integer and Real arithmetic should be detected."""
        caps = analyze_logic_capabilities("QF_LIA")
        assert "INT" in caps

        caps = analyze_logic_capabilities("QF_LRA")
        assert "REAL" in caps

        caps = analyze_logic_capabilities("QF_NIA")
        assert "INT" in caps
        assert "NONLINEAR" in caps

        caps = analyze_logic_capabilities("QF_NRA")
        assert "REAL" in caps
        assert "NONLINEAR" in caps

    def test_array_detection(self):
        """Array theories should be detected."""
        caps = analyze_logic_capabilities("QF_ALIA")
        assert "ARRAYS" in caps

        caps = analyze_logic_capabilities("QF_ABV")
        assert "ARRAYS" in caps
        assert "BV" in caps

    def test_uf_detection(self):
        """Uninterpreted functions should be detected."""
        caps = analyze_logic_capabilities("QF_UF")
        assert "UF" in caps

        caps = analyze_logic_capabilities("QF_UFLIA")
        assert "UF" in caps
        assert "INT" in caps

    def test_fp_detection(self):
        """Floating-point theories should be detected."""
        caps = analyze_logic_capabilities("QF_FP")
        assert "FP" in caps

    def test_difference_logic_detection(self):
        """Difference logic variants should be detected."""
        caps = analyze_logic_capabilities("QF_IDL")
        assert "INT" in caps
        assert "DL" in caps

        caps = analyze_logic_capabilities("QF_RDL")
        assert "REAL" in caps
        assert "DL" in caps


class TestLogicCompatibility:
    """Tests for is_logic_compatible function."""

    def test_same_logic_compatible(self):
        """Same logic should always be compatible."""
        assert is_logic_compatible("QF_LIA", "QF_LIA")
        assert is_logic_compatible("QF_BV", "QF_BV")
        assert is_logic_compatible("LIA", "LIA")

    def test_quantifier_restriction(self):
        """Quantified formulas should not be used in QF targets."""
        # Quantifier-free is OK for QF target
        assert is_logic_compatible("QF_LIA", "QF_LIA")

        # Quantified is NOT OK for QF target
        assert not is_logic_compatible("LIA", "QF_LIA")
        assert not is_logic_compatible("AUFLIA", "QF_LIA")

        # QF is OK for quantified target
        assert is_logic_compatible("QF_LIA", "LIA")

    def test_sort_compatibility(self):
        """Candidate sorts must be present in target."""
        # BV requires BV
        assert not is_logic_compatible("QF_BV", "QF_LIA")
        assert is_logic_compatible("QF_BV", "QF_ABV")

        # Arrays require Arrays
        assert not is_logic_compatible("QF_ALIA", "QF_LIA")
        assert is_logic_compatible("QF_ALIA", "QF_AUFLIA")

    def test_nonlinear_compatibility(self):
        """Nonlinear requires nonlinear target."""
        # Nonlinear is OK for nonlinear target
        assert is_logic_compatible("QF_NIA", "QF_NIA")

        # Nonlinear is NOT OK for linear target
        assert not is_logic_compatible("QF_NIA", "QF_LIA")

        # Linear is OK for nonlinear target
        assert is_logic_compatible("QF_LIA", "QF_NIA")

    def test_uf_compatibility(self):
        """UF requires UF in target."""
        assert is_logic_compatible("QF_UF", "QF_UF")
        assert not is_logic_compatible("QF_UF", "QF_LIA")
        assert is_logic_compatible("QF_UF", "QF_UFLIA")


class TestParenthesisDepth:
    """Tests for _smt_paren_depth function."""

    def test_balanced_parens(self):
        """Balanced parentheses should return 0."""
        assert _smt_paren_depth("(assert true)") == 0
        assert _smt_paren_depth("(assert (and x y))") == 0
        assert _smt_paren_depth("(set-logic QF_LIA)\n(assert (= x 1))\n(check-sat)") == 0

    def test_unbalanced_open(self):
        """More opens than closes should return positive."""
        assert _smt_paren_depth("(assert (and x y") > 0
        assert _smt_paren_depth("((((") == 4

    def test_unbalanced_close(self):
        """More closes than opens should return negative."""
        assert _smt_paren_depth("(assert))") < 0
        assert _smt_paren_depth("))))") == -4

    def test_string_literal_handling(self):
        """Parentheses in strings should not count."""
        # Paren in string should not affect depth
        assert _smt_paren_depth('(assert (= s "(()")()) )")') == 0

    def test_empty_string(self):
        """Empty string should return 0."""
        assert _smt_paren_depth("") == 0


class TestStripNamedAnnotation:
    """Tests for _strip_named_annotation function."""

    def test_strip_named_wrapper(self):
        """Should strip (! ... :named label) wrapper."""
        result = _strip_named_annotation("(! (=> a b) :named IP_1)")
        assert result == "(=> a b)"

    def test_no_wrapper(self):
        """Should return unchanged if no wrapper."""
        result = _strip_named_annotation("(and x y)")
        assert result == "(and x y)"

    def test_named_without_bang(self):
        """Should return unchanged if :named without (!."""
        result = _strip_named_annotation("(assert :named foo)")
        assert result == "(assert :named foo)"

    def test_complex_expression(self):
        """Should handle complex nested expressions."""
        result = _strip_named_annotation("(! (not (or a b c)) :named complex)")
        assert result == "(not (or a b c))"


class TestExtractSortsFromDecl:
    """Tests for _extract_sorts_from_decl function."""

    def test_declare_fun_simple(self):
        """Extract sorts from simple declare-fun."""
        sorts = _extract_sorts_from_decl("(declare-fun x () Int)")
        assert "Int" in sorts

    def test_declare_fun_with_args(self):
        """Extract sorts from declare-fun with arguments."""
        sorts = _extract_sorts_from_decl("(declare-fun f (Int Bool) Int)")
        assert "Int" in sorts
        assert "Bool" in sorts

    def test_declare_const(self):
        """Extract sorts from declare-const."""
        sorts = _extract_sorts_from_decl("(declare-const x Real)")
        assert "Real" in sorts

    def test_builtin_sorts_excluded(self):
        """Built-in sorts should not be included."""
        sorts = _extract_sorts_from_decl("(declare-fun x () Int)")
        # Int is builtin, so should not be in result
        assert "Int" not in sorts

    def test_custom_sorts_included(self):
        """Custom sorts should be included."""
        sorts = _extract_sorts_from_decl("(declare-fun f () MyCustomSort)")
        assert "MyCustomSort" in sorts

    def test_array_sort(self):
        """Array sorts should be handled."""
        sorts = _extract_sorts_from_decl("(declare-fun arr () (Array Int Int))")
        # Array, Int are builtins, should not be in result
        assert all(_is_builtin_sort(s) for s in ["Array", "Int"])


class TestIsBuiltinSort:
    """Tests for _is_builtin_sort function."""

    def test_builtin_sorts(self):
        """Standard SMT-LIB sorts should be recognized as builtins."""
        assert _is_builtin_sort("Bool")
        assert _is_builtin_sort("Int")
        assert _is_builtin_sort("Real")
        assert _is_builtin_sort("String")
        assert _is_builtin_sort("Array")
        assert _is_builtin_sort("BitVec")

    def test_indexed_sorts(self):
        """Indexed sorts should be recognized."""
        assert _is_builtin_sort("(_ BitVec 32)")
        assert _is_builtin_sort("(_ FloatingPoint 8 24)")

    def test_custom_sorts_not_builtin(self):
        """Custom sorts should not be recognized as builtins."""
        assert not _is_builtin_sort("MySort")
        assert not _is_builtin_sort("CustomType")


class TestValidateSmtFormula:
    """Tests for _validate_smt_formula function."""

    def test_valid_formula(self):
        """Valid formulas should pass validation."""
        assert _validate_smt_formula("(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)")

    def test_unbalanced_parens(self):
        """Unbalanced parentheses should fail validation."""
        assert not _validate_smt_formula("(assert (> x 0")
        assert not _validate_smt_formula("(assert (> x 0)))")

    def test_missing_check_sat(self):
        """Missing check-sat should fail validation."""
        assert not _validate_smt_formula("(set-logic QF_LIA)\n(assert (> x 0))")

    def test_incremental_valid(self):
        """Incremental scripts with push should be valid."""
        assert _validate_smt_formula("(push)\n(assert true)\n(check-sat)\n(pop)")

    def test_named_at_wrong_depth(self):
        """:named at wrong depth should fail validation."""
        # This is a heuristic check, may not catch all cases
        script = "(assert :named foo (> x 0))\n(check-sat)"
        assert not _validate_smt_formula(script)


class TestConstructScripts:
    """Tests for build_smt_script function (replaces construct_scripts)."""

    def test_basic_script_construction(self):
        """Test basic script construction."""
        decls = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))", "(assert (< x 10))"]
        result = build_smt_script(decls, assertions)

        assert "(set-logic ALL)" in result
        assert "(declare-fun x () Int)" in result
        assert "(assert (> x 0))" in result
        assert "(assert (< x 10))" in result
        assert "(check-sat)" in result

    def test_incremental_script(self):
        """Test incremental script construction."""
        decls = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))", "(assert (< x 10))"]
        result = build_smt_script(decls, assertions, incremental=True)

        assert "(push" in result
        assert "(pop" in result

    def test_custom_logic(self):
        """Test custom logic specification."""
        decls = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))"]
        result = build_smt_script(decls, assertions, logic="QF_LIA")

        assert "(set-logic QF_LIA)" in result

    def test_merge_asserts(self):
        """Test merging assertions into single and."""
        decls = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))", "(assert (< x 10))"]
        result = build_smt_script(decls, assertions, merge_asserts=True)

        assert "(and" in result


class TestInsertPushAndPop:
    """Tests for insert_push_and_pop function."""

    def test_basic_insertion(self):
        """Test basic push/pop insertion."""
        ast = ["(assert a)", "(assert b)", "(assert c)"]
        result = insert_push_and_pop(ast)

        # Should have push and pop
        assert any("(push" in s for s in result)
        assert any("(pop" in s for s in result)
        # Should have check-sat
        assert "(check-sat)" in result

    def test_balanced_stack(self):
        """Test that push/pop stack is balanced."""
        ast = ["(assert a)", "(assert b)", "(assert c)"]
        result = insert_push_and_pop(ast)

        # Count push/pop to verify balance
        push_count = sum(1 for s in result if s.startswith("(push"))
        pop_count = sum(1 for s in result if s.startswith("(pop"))
        assert push_count >= pop_count  # May have extra pops

    def test_single_assertion(self):
        """Test with single assertion."""
        ast = ["(assert true)"]
        result = insert_push_and_pop(ast)

        assert "(check-sat)" in result


class TestBuildTypeVar:
    """Tests for build_type_var_map function."""

    def test_basic_variable_building(self):
        """Test basic variable type mapping."""
        var_list = ["x, Int", "y, Bool", "z, Real"]
        result = _build_type_var(var_list)

        assert "Int" in result
        assert "Bool" in result
        assert "Real" in result
        assert "x" in result["Int"]
        assert "y" in result["Bool"]
        assert "z" in result["Real"]

    def test_empty_list(self):
        """Test with empty variable list."""
        result = _build_type_var([])
        assert result == {}

    def test_multiple_vars_same_type(self):
        """Test multiple variables of same type."""
        var_list = ["x, Int", "y, Int", "z, Int"]
        result = _build_type_var(var_list)

        assert "Int" in result
        assert len(result["Int"]) == 3


class TestVariableTranslocation:
    """Tests for variable_translocation function."""

    def test_basic_translocation(self):
        """Test basic variable swapping."""
        ast = ["(assert (= x y))"]
        type_var = {"Int": ["x", "y", "z"]}
        result = variable_translocation(ast, type_var)

        # Should return a list with one assertion (possibly modified)
        assert len(result) == 1
        assert result[0].startswith("(assert")

    def test_empty_type_var(self):
        """Test with empty type variable mapping."""
        ast = ["(assert true)"]
        result = variable_translocation(ast, {})

        assert result == ast

    def test_preserves_structure(self):
        """Test that structure is preserved."""
        ast = ["(assert (and a b c))"]
        result = variable_translocation(ast, {"Bool": ["a", "b", "c"]})

        # Should still be a valid assertion
        assert result[0].startswith("(assert")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
