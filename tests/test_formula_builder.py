"""
Unit tests for formula_builder module (chimera/core/formula_builder.py).

Tests cover:
- Parenthesis depth calculation
- Parenthesis balancing
- SMT formula validation
- Named annotation stripping
- Formula formatting
- Incremental mode (push/pop)
- Variable type mapping
- Variable translocation
- SMT script building
"""

import pytest
import re
from chimera.core.formula_builder import (
    smt_paren_depth,
    balance_parentheses,
    validate_smt_formula,
    strip_named_annotation,
    format_smt_string,
    insert_push_and_pop,
    is_valid_symbol_name,
    build_type_var_map,
    variable_translocation,
    extract_function_name,
    build_smt_script,
)


class TestSmtParenDepth:
    """Tests for smt_paren_depth function."""

    def test_balanced_parens(self):
        """Test balanced parentheses return 0."""
        assert smt_paren_depth("(assert true)") == 0
        assert smt_paren_depth("(assert (and x y))") == 0
        assert smt_paren_depth("(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)") == 0

    def test_unbalanced_open(self):
        """Test more opens than closes returns positive."""
        assert smt_paren_depth("(assert (and x y") > 0
        assert smt_paren_depth("((((") == 4
        assert smt_paren_depth("(declare-fun x () Int") > 0

    def test_unbalanced_close(self):
        """Test more closes than opens returns negative."""
        assert smt_paren_depth("(assert))") < 0
        assert smt_paren_depth("))))") == -4

    def test_string_literal_parens(self):
        """Test parentheses in strings are not counted."""
        # Parens inside strings should not affect depth
        assert smt_paren_depth('(assert (= s "(()())"))') == 0
        assert smt_paren_depth('(assert (str.prefixof "(" s))') == 0

    def test_empty_string(self):
        """Test empty string returns 0."""
        assert smt_paren_depth("") == 0

    def test_complex_nested(self):
        """Test complex nested expressions."""
        formula = """
        (assert (forall ((x Int))
            (=> (and (> x 0) (< x 10))
                (exists ((y Int))
                    (= (+ x y) 15)))))
        """
        assert smt_paren_depth(formula) == 0

    def test_escaped_quotes(self):
        """Test handling of escaped quotes in strings."""
        # Escaped quote should not toggle string mode
        assert smt_paren_depth('(assert (= s "test\\"string"))') == 0


class TestBalanceParentheses:
    """Tests for balance_parentheses function."""

    def test_balanced_unchanged(self):
        """Test balanced formulas are unchanged."""
        formula = "(assert (and x y))"
        assert balance_parentheses(formula) == formula

    def test_adds_closing_parens(self):
        """Test adding missing closing parentheses."""
        assert balance_parentheses("(assert (and x y") == "(assert (and x y))"
        assert balance_parentheses("(declare-fun x () Int") == "(declare-fun x () Int)"

    def test_multiple_missing(self):
        """Test adding multiple missing parentheses."""
        result = balance_parentheses("((((")
        assert result == "((((" + "))))"
        assert smt_paren_depth(result) == 0

    def test_does_not_remove_excess(self):
        """Test that excess closing parens are not removed."""
        result = balance_parentheses("(assert))")
        # Should NOT remove the extra )
        assert result == "(assert))"


class TestValidateSmtFormula:
    """Tests for validate_smt_formula function."""

    def test_valid_formula(self):
        """Test valid formula passes validation."""
        formula = "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)"
        assert validate_smt_formula(formula) is True

    def test_unbalanced_parens_fails(self):
        """Test unbalanced parentheses fails."""
        assert validate_smt_formula("(assert (> x 0)") is False
        assert validate_smt_formula("(assert (> x 0)))") is False

    def test_missing_check_sat_fails(self):
        """Test missing check-sat fails."""
        formula = "(set-logic QF_LIA)\n(assert (> x 0))"
        assert validate_smt_formula(formula) is False

    def test_incremental_valid(self):
        """Test incremental script with push is valid."""
        formula = "(push)\n(assert true)\n(check-sat)\n(pop)"
        assert validate_smt_formula(formula) is True

    def test_named_annotation_wrong_depth(self):
        """Test :named at wrong depth fails validation."""
        # Named annotation should be inside (! ...)
        formula = "(assert :named foo (> x 0))\n(check-sat)"
        assert validate_smt_formula(formula) is False

    def test_valid_named_annotation(self):
        """Test properly placed :named is valid."""
        formula = "(set-logic QF_LIA)\n(assert (! (> x 0) :named pos-x))\n(check-sat)"
        assert validate_smt_formula(formula) is True

    def test_empty_formula_fails(self):
        """Test empty formula fails."""
        assert validate_smt_formula("") is False


class TestStripNamedAnnotation:
    """Tests for strip_named_annotation function."""

    def test_strip_named_wrapper(self):
        """Test stripping (! ... :named label) wrapper."""
        assert strip_named_annotation("(! (=> a b) :named IP_1)") == "(=> a b)"
        assert strip_named_annotation("(! (and x y) :named conj)") == "(and x y)"

    def test_no_wrapper_unchanged(self):
        """Test that formulas without wrapper are unchanged."""
        assert strip_named_annotation("(and x y)") == "(and x y)"
        assert strip_named_annotation("(or a b)") == "(or a b)"

    def test_named_without_bang_unchanged(self):
        """Test :named without (! is unchanged."""
        result = strip_named_annotation("(assert :named foo)")
        assert result == "(assert :named foo)"

    def test_complex_expression(self):
        """Test stripping from complex expression."""
        result = strip_named_annotation("(! (not (or a b c)) :named complex)")
        assert result == "(not (or a b c))"

    def test_preserves_whitespace(self):
        """Test that internal whitespace is preserved."""
        result = strip_named_annotation("(! (and   x   y) :named test)")
        assert "and   x   y" in result

    def test_multiple_named(self):
        """Test expression with multiple named annotations."""
        # Only outer should be stripped
        result = strip_named_annotation("(! (! (and x y) :named inner) :named outer)")
        assert ":named inner" in result
        assert ":named outer" not in result


class TestFormatSmtString:
    """Tests for format_smt_string function."""

    def test_preserves_content(self):
        """Test that formatting preserves formula content."""
        formula = "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)"
        formatted = format_smt_string(formula)
        assert "(set-logic QF_LIA)" in formatted
        assert "(assert (> x 0))" in formatted
        assert "(check-sat)" in formatted

    def test_removes_excessive_blank_lines(self):
        """Test that excessive blank lines are removed."""
        formula = "(set-logic QF_LIA)\n\n\n\n\n(assert true)\n(check-sat)"
        formatted = format_smt_string(formula)
        # Should have at most 2 consecutive newlines
        assert "\n\n\n" not in formatted

    def test_normalizes_line_endings(self):
        """Test that line endings are normalized to \n."""
        formula = "(assert true)\r\n(check-sat)"
        formatted = format_smt_string(formula)
        assert "\r\n" not in formatted
        assert "\r" not in formatted

    def test_strips_whitespace(self):
        """Test that leading/trailing whitespace is stripped."""
        formula = "  \n  (assert true)  \n  "
        formatted = format_smt_string(formula)
        assert formatted.startswith("(assert")
        assert formatted.endswith(")")


class TestInsertPushAndPop:
    """Tests for insert_push_and_pop function."""

    def test_basic_insertion(self):
        """Test basic push/pop insertion."""
        assertions = ["(assert a)", "(assert b)", "(assert c)"]
        result = insert_push_and_pop(assertions)

        # Should have push and pop
        assert any("(push" in s for s in result)
        assert any("(pop" in s for s in result)
        # Should have check-sat
        assert "(check-sat)" in result

    def test_single_assertion(self):
        """Test with single assertion."""
        assertions = ["(assert true)"]
        result = insert_push_and_pop(assertions)
        assert "(check-sat)" in result

    def test_empty_assertions(self):
        """Test with empty assertions list."""
        result = insert_push_and_pop([])
        assert "(check-sat)" in result

    def test_assertions_without_wrapper(self):
        """Test that bare assertions get wrapped."""
        assertions = ["(> x 0)", "(< y 10)"]
        result = insert_push_and_pop(assertions)
        # Should add (assert ...) wrapper
        result_str = " ".join(result)
        assert "(assert" in result_str


class TestIsValidSymbolName:
    """Tests for is_valid_symbol_name function."""

    def test_valid_simple_names(self):
        """Test valid simple symbol names."""
        assert is_valid_symbol_name("x")
        assert is_valid_symbol_name("var1")
        assert is_valid_symbol_name("my-var")
        assert is_valid_symbol_name("my_var")
        assert is_valid_symbol_name("var.name")

    def test_valid_special_chars(self):
        """Test valid names with special characters."""
        assert is_valid_symbol_name("var!")
        assert is_valid_symbol_name("var?")
        assert is_valid_symbol_name("var+")
        assert is_valid_symbol_name("var*")

    def test_reserved_names_invalid(self):
        """Test that reserved names are invalid."""
        assert not is_valid_symbol_name("Int")
        assert not is_valid_symbol_name("Bool")
        assert not is_valid_symbol_name("assert")
        assert not is_valid_symbol_name("declare-fun")
        assert not is_valid_symbol_name("forall")
        assert not is_valid_symbol_name("exists")

    def test_empty_invalid(self):
        """Test that empty string is invalid."""
        assert not is_valid_symbol_name("")

    def test_spaces_invalid(self):
        """Test that names with spaces are invalid."""
        assert not is_valid_symbol_name("my var")
        assert not is_valid_symbol_name("var name")


class TestBuildTypeVarMap:
    """Tests for build_type_var_map function."""

    def test_basic_mapping(self):
        """Test basic type-to-variable mapping."""
        var_list = ["x, Int", "y, Bool", "z, Real"]
        result = build_type_var_map(var_list)

        assert "Int" in result
        assert "Bool" in result
        assert "Real" in result
        assert "x" in result["Int"]
        assert "y" in result["Bool"]
        assert "z" in result["Real"]

    def test_multiple_vars_same_type(self):
        """Test multiple variables of same type."""
        var_list = ["x, Int", "y, Int", "z, Int"]
        result = build_type_var_map(var_list)

        assert "Int" in result
        assert len(result["Int"]) == 3
        assert "x" in result["Int"]
        assert "y" in result["Int"]
        assert "z" in result["Int"]

    def test_empty_list(self):
        """Test with empty variable list."""
        result = build_type_var_map([])
        assert result == {}

    def test_malformed_entries(self):
        """Test handling of malformed entries."""
        var_list = ["x, Int", "malformed", "z, Real"]
        result = build_type_var_map(var_list)

        assert "Int" in result
        assert "Real" in result
        assert "x" in result["Int"]
        assert "z" in result["Real"]


class TestVariableTranslocation:
    """Tests for variable_translocation function."""

    def test_basic_translocation(self):
        """Test basic variable swapping."""
        assertions = ["(assert (= x y))"]
        type_var = {"Int": ["x", "y", "z"]}
        result = variable_translocation(assertions, type_var)

        # Should return a list with one assertion
        assert len(result) == 1
        assert result[0].startswith("(assert")

    def test_empty_type_var(self):
        """Test with empty type variable mapping."""
        assertions = ["(assert true)"]
        result = variable_translocation(assertions, {})

        assert result == assertions

    def test_preserves_structure(self):
        """Test that structure is preserved."""
        assertions = ["(assert (and a b c))"]
        result = variable_translocation(assertions, {"Bool": ["a", "b", "c"]})

        # Should still be a valid assertion
        assert result[0].startswith("(assert")

    def test_no_matching_vars(self):
        """Test with no matching variables."""
        assertions = ["(assert (> x 0))"]
        result = variable_translocation(assertions, {"Real": ["r", "s"]})

        # Should return unchanged (no Int vars to swap)
        assert result == assertions


class TestExtractFunctionName:
    """Tests for extract_function_name function."""

    def test_declare_fun(self):
        """Test extracting name from declare-fun."""
        assert extract_function_name("(declare-fun f (Int Bool) Int)") == "f"
        assert extract_function_name("(declare-fun my-func () Real)") == "my-func"

    def test_declare_const(self):
        """Test extracting name from declare-const."""
        assert extract_function_name("(declare-const x Int)") == "x"
        assert extract_function_name("(declare-const state Bool)") == "state"

    def test_define_fun(self):
        """Test extracting name from define-fun."""
        assert extract_function_name("(define-fun f ((x Int)) Int x)") == "f"

    def test_define_const(self):
        """Test extracting name from define-const."""
        assert extract_function_name("(define-const x Int 42)") == "x"

    def test_invalid_declaration(self):
        """Test handling of invalid declaration."""
        assert extract_function_name("not a declaration") is None
        assert extract_function_name("(invalid x)") is None


class TestBuildSmtScript:
    """Tests for build_smt_script function."""

    def test_basic_script(self):
        """Test basic script construction."""
        declarations = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))"]

        result = build_smt_script(declarations, assertions)

        assert "(set-logic ALL)" in result
        assert "(declare-fun x () Int)" in result
        assert "(assert (> x 0))" in result
        assert "(check-sat)" in result

    def test_custom_logic(self):
        """Test with custom logic."""
        declarations = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))"]

        result = build_smt_script(declarations, assertions, logic="QF_LIA")

        assert "(set-logic QF_LIA)" in result

    def test_deduplicate_declarations(self):
        """Test that duplicate declarations are removed."""
        declarations = [
            "(declare-fun x () Int)",
            "(declare-fun x () Int)",  # duplicate
            "(declare-fun y () Int)",
        ]
        assertions = ["(assert true)"]

        result = build_smt_script(declarations, assertions)

        # Should only appear once
        assert result.count("(declare-fun x () Int)") == 1

    def test_incremental_mode(self):
        """Test incremental mode adds push/pop."""
        declarations = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))", "(assert (< x 10))"]

        result = build_smt_script(declarations, assertions, incremental=True)

        assert "(push" in result
        assert "(pop" in result

    def test_merge_asserts(self):
        """Test merging assertions into conjunction."""
        declarations = ["(declare-fun x () Int)"]
        assertions = ["(assert (> x 0))", "(assert (< x 10))"]

        result = build_smt_script(declarations, assertions, merge_asserts=True)

        # Should have single (assert (and ...))
        assert "(assert (and" in result

    def test_bare_assertions_wrapped(self):
        """Test that bare assertions get wrapped."""
        declarations = []
        assertions = ["> x 0"]  # No (assert ...) wrapper

        result = build_smt_script(declarations, assertions)

        assert "(assert > x 0)" in result

    def test_multiple_assertions(self):
        """Test multiple assertions are all included."""
        declarations = []
        assertions = ["(assert a)", "(assert b)", "(assert c)"]

        result = build_smt_script(declarations, assertions)

        assert "(assert a)" in result
        assert "(assert b)" in result
        assert "(assert c)" in result

    def test_empty_assertions(self):
        """Test with empty assertions."""
        declarations = ["(declare-fun x () Int)"]
        assertions = []

        result = build_smt_script(declarations, assertions)

        assert "(check-sat)" in result


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
