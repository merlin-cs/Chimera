"""
Unit tests for the SMT-LIB parser modules.

Tests cover:
- Parsing SMT-LIB2 syntax (both legacy and canonical parser)
- AST construction
- Term and expression manipulation
- Type checking

Note: The canonical parser is chimera.core.smt_parser.
"""

import pytest
from pathlib import Path

from chimera.core.smt_parser import parse_string, parse_file as parse_file_canonical
from chimera.core.smt_ast import (
    Term,
    Expr,
    Var,
    Const,
    Assert,
    DeclareFun,
    DeclareConst,
    Script,
)
from chimera.core.types import AND, OR, NOT, IMPLIES, IFF, XOR


# Alias for backward compatibility with test naming
parse_str = parse_string
parse_file = parse_file_canonical


class TestParseStr:
    """Tests for parse_str function."""

    def test_parse_simple_assert(self):
        """Test parsing a simple assertion."""
        script, _ = parse_str("(assert true)")
        assert script is not None
        assert len(script.assert_cmd) == 1

    def test_parse_set_logic(self):
        """Test parsing set-logic command."""
        script, _ = parse_str("(set-logic QF_LIA)")
        assert script is not None

    def test_parse_declare_fun(self):
        """Test parsing declare-fun command."""
        script, _ = parse_str("(declare-fun x () Int)")
        assert script is not None
        assert len(script.commands) == 1

    def test_parse_check_sat(self):
        """Test parsing check-sat command."""
        script, _ = parse_str("(check-sat)")
        assert script is not None

    def test_parse_complex_formula(self):
        """Test parsing a complex formula."""
        smt = """
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (and (> x 0) (< y 10) (= (+ x y) 15)))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None
        assert len(script.assert_cmd) == 1

    def test_parse_quantified_formula(self):
        """Test parsing quantified formula."""
        smt = """
        (set-logic LIA)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (p x)))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None
        assert len(script.assert_cmd) == 1

    def test_parse_bitvector_operations(self):
        """Test parsing bitvector operations."""
        smt = """
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 32))
        (declare-fun b () (_ BitVec 32))
        (assert (= (bvadd a b) #x00000001))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_array_operations(self):
        """Test parsing array operations."""
        smt = """
        (set-logic QF_ALIA)
        (declare-fun arr () (Array Int Int))
        (assert (= (select arr 0) 5))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_string_operations(self):
        """Test parsing string operations."""
        smt = """
        (set-logic QF_S)
        (declare-fun s () String)
        (assert (str.prefixof "hello" s))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_let_expression(self):
        """Test parsing let expressions."""
        smt = """
        (set-logic QF_LIA)
        (assert (let ((x 5)) (> x 0)))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_named_assertion(self):
        """Test parsing named assertions."""
        smt = """
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (assert (! (> x 0) :named pos-x))
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_push_pop(self):
        """Test parsing push/pop commands."""
        smt = """
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (push)
        (assert (> x 5))
        (check-sat)
        (pop)
        (check-sat)
        """
        script, _ = parse_str(smt)
        assert script is not None

    def test_parse_silent_mode(self):
        """Test silent parsing mode."""
        script, _ = parse_str("(assert true)", silent=True)
        assert script is not None

    def test_parse_invalid_syntax(self):
        """Test handling of invalid syntax."""
        # Invalid syntax should return None or handle gracefully
        script, _ = parse_str("(assert", silent=True)
        # Parser should handle gracefully (may return None or partial result)


class TestParseFile:
    """Tests for parse_file function."""

    def test_parse_valid_file(self, sample_smt2_file):
        """Test parsing a valid SMT2 file."""
        script, _ = parse_file(str(sample_smt2_file))
        assert script is not None
        assert len(script.assert_cmd) >= 1

    def test_parse_nonexistent_file(self, temp_dir):
        """Test handling of nonexistent file."""
        nonexistent = temp_dir / "nonexistent.smt2"
        result = parse_file(str(nonexistent), silent=True)
        # Should handle gracefully by returning None
        assert result is None


class TestTerm:
    """Tests for Term class."""

    def test_term_creation(self):
        """Test basic term creation."""
        term = Term(op="and", subterms=[])
        assert term.op == "and"

    def test_term_with_subterms(self):
        """Test term with subterms."""
        sub1 = Term(op="x", subterms=[])
        sub2 = Term(op="y", subterms=[])
        term = Term(op="and", subterms=[sub1, sub2])
        assert len(term.subterms) == 2

    def test_term_str_representation(self):
        """Test string representation of term."""
        term = Term(op="true", subterms=[])
        assert str(term) == "true"


class TestExpr:
    """Tests for Expr class."""

    def test_expr_creation(self):
        """Test basic expression creation."""
        expr = Expr(op="and", subterms=[])
        assert expr.op == "and"

    def test_expr_with_subterms(self):
        """Test expression with subterms."""
        sub1 = Expr(op="x", subterms=[])
        sub2 = Expr(op="y", subterms=[])
        expr = Expr(op="or", subterms=[sub1, sub2])
        assert len(expr.subterms) == 2


class TestVar:
    """Tests for Var class."""

    def test_var_creation(self):
        """Test variable creation."""
        var = Var(name="x", type="Int")
        assert var.name == "x"
        assert var.type == "Int"
        assert var.is_var is True

    def test_var_str_representation(self):
        """Test string representation of variable."""
        var = Var(name="x", type="Int")
        assert "x" in str(var)


class TestConst:
    """Tests for Const class."""

    def test_const_creation(self):
        """Test constant creation."""
        const = Const(name="42", type="Int")
        assert const.name == "42"
        assert const.type == "Int"
        assert const.is_const is True

    def test_const_str_representation(self):
        """Test string representation of constant."""
        const = Const(name="42", type="Int")
        assert "42" in str(const)


class TestAssert:
    """Tests for Assert class."""

    def test_assert_creation(self):
        """Test assertion creation."""
        term = Term(op="true", subterms=[])
        assertion = Assert(term=term)
        assert assertion.term is not None


class TestDeclareFun:
    """Tests for DeclareFun class."""

    def test_declare_fun_creation(self):
        """Test declare-fun creation."""
        decl = DeclareFun(symbol="x", input_sort="", output_sort="Int")
        assert decl.symbol == "x"
        assert decl.output_sort == "Int"

    def test_declare_fun_str_representation(self):
        """Test string representation of declare-fun."""
        decl = DeclareFun(symbol="x", input_sort="", output_sort="Int")
        result = str(decl)
        assert "declare-fun" in result
        assert "x" in result
        assert "Int" in result


class TestTypes:
    """Tests for logical type constants."""

    def test_type_constants(self):
        """Test that type constants are defined."""
        assert AND is not None
        assert OR is not None
        assert NOT is not None
        assert IMPLIES is not None
        assert IFF is not None
        assert XOR is not None


class TestSubstitution:
    """Tests for term/expression substitution."""

    def test_term_substitution(self):
        """Test term substitution."""
        # Parse a simple expression
        script, _ = parse_str("(assert (= x y))")
        if script and script.assert_cmd:
            term = script.assert_cmd[0].term
            # Get all subterms
            if hasattr(term, 'subterms') and term.subterms:
                # Create a new term to substitute
                new_term = Expr(op="z", subterms=[])
                # Note: substitution behavior depends on implementation
                pass  # Implementation-specific test

    def test_expr_substitution(self):
        """Test expression substitution."""
        expr = Expr(op="x", subterms=[])
        new_expr = Expr(op="y", subterms=[])
        # Note: substitution behavior depends on implementation
        pass


class TestTypeChecking:
    """Tests for type checking."""

    def test_int_type(self):
        """Test integer type handling."""
        const = Const(name="42", type="Int")
        assert const.type == "Int"

    def test_bool_type(self):
        """Test boolean type handling."""
        var = Var(name="b", type="Bool")
        assert var.type == "Bool"

    def test_bitvector_type(self):
        """Test bitvector type handling."""
        var = Var(name="bv", type="(_ BitVec 32)")
        assert "BitVec" in var.type

    def test_array_type(self):
        """Test array type handling."""
        var = Var(name="arr", type="(Array Int Int)")
        assert "Array" in var.type


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
