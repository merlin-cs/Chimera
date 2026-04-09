"""
Unit tests for smt_ast module (chimera/core/smt_ast.py).

Tests cover:
- Term creation and properties
- TermKind classification
- Variable, Constant, Expression factories
- Quantifier and LetBinding creation
- Script class
- AST traversal (visitors, transformers)
- Substitution operations
- SMT-LIB command classes
"""

import pytest
from chimera.core.smt_ast import (
    Term,
    TermKind,
    Var,
    Const,
    Expr,
    Quantifier,
    LetBinding,
    LabeledTerm,
    Hole,
    make_hole_name,
    is_hole,
    DeclareConst,
    DeclareFun,
    Assert,
    AssertSoft,
    Define,
    DefineConst,
    DefineFun,
    CheckSat,
    CheckSatAssuming,
    Push,
    Pop,
    GetValue,
    Simplify,
    Minimize,
    Maximize,
    Display,
    Eval,
    SMTLIBCommand,
    Script,
    AstVisitorBase,
    AstTransformer,
    HoleCollector,
    VariableCollector,
    SubstitutionTransformer,
    SkeletonExtractor,
    collect_basic_subterms,
    collect_all_basic_subformulas,
)
from chimera.core.types import AND, OR, NOT, IMPLIES


class TestTermKind:
    """Tests for TermKind enum."""

    def test_all_kinds_exist(self):
        """Test that all term kinds are defined."""
        assert TermKind.VARIABLE
        assert TermKind.CONSTANT
        assert TermKind.EXPRESSION
        assert TermKind.QUANTIFIER
        assert TermKind.LET_BINDING
        assert TermKind.LABELED
        assert TermKind.HOLE
        assert TermKind.UNKNOWN


class TestVar:
    """Tests for Var factory function."""

    def test_var_creation(self):
        """Test basic variable creation."""
        var = Var("x", "Int")
        assert var.name == "x"
        assert var.type == "Int"
        assert var.is_var is True
        assert var.is_const is False

    def test_var_kind(self):
        """Test that Var has VARIABLE kind."""
        var = Var("x", "Int")
        assert var.kind == TermKind.VARIABLE

    def test_var_str_representation(self):
        """Test string representation of variable."""
        var = Var("x", "Int")
        assert str(var) == "x"

    def test_var_repr(self):
        """Test repr of variable."""
        var = Var("x", "Int")
        assert "x" in repr(var)
        assert "Int" in repr(var)


class TestConst:
    """Tests for Const factory function."""

    def test_const_creation(self):
        """Test basic constant creation."""
        const = Const("42", "Int")
        assert const.name == "42"
        assert const.type == "Int"
        assert const.is_const is True
        assert const.is_var is False

    def test_const_kind(self):
        """Test that Const has CONSTANT kind."""
        const = Const("42", "Int")
        assert const.kind == TermKind.CONSTANT

    def test_const_without_type(self):
        """Test constant without explicit type."""
        const = Const("true")
        assert const.name == "true"
        assert const.is_const is True


class TestExpr:
    """Tests for Expr factory function."""

    def test_expr_creation(self):
        """Test basic expression creation."""
        expr = Expr("+", [Var("x", "Int"), Const("1", "Int")])
        assert expr.op == "+"
        assert len(expr.subterms) == 2

    def test_expr_kind(self):
        """Test that Expr has EXPRESSION kind."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        assert expr.kind == TermKind.EXPRESSION

    def test_expr_str_representation(self):
        """Test string representation of expression."""
        expr = Expr("and", [Const("true", "Bool"), Const("false", "Bool")])
        result = str(expr)
        assert "(and" in result
        assert "true" in result
        assert "false" in result

    def test_expr_depth(self):
        """Test expression depth calculation."""
        # Simple: depth 0
        simple = Const("true", "Bool")
        assert simple.depth == 0

        # Nested: depth 2
        inner = Expr(NOT, [Var("a", "Bool")])
        middle = Expr(AND, [inner, Var("b", "Bool")])
        outer = Expr(OR, [middle, Var("c", "Bool")])
        assert outer.depth == 2

    def test_expr_size(self):
        """Test expression size calculation."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        assert expr.size == 3  # 1 AND + 2 vars


class TestQuantifier:
    """Tests for Quantifier factory function."""

    def test_forall_creation(self):
        """Test forall quantifier creation."""
        q = Quantifier("forall", (["x", "y"], ["Int", "Int"]), [Var("x", "Int")])
        assert q.quantifier == "forall"
        assert q.kind == TermKind.QUANTIFIER

    def test_exists_creation(self):
        """Test exists quantifier creation."""
        q = Quantifier("exists", (["x"], ["Int"]), [Var("x", "Int")])
        assert q.quantifier == "exists"
        assert q.kind == TermKind.QUANTIFIER

    def test_quantifier_str(self):
        """Test string representation of quantifier."""
        q = Quantifier("forall", (["x"], ["Int"]), [Expr(">", [Var("x", "Int"), Const("0", "Int")])])
        result = str(q)
        assert "(forall" in result
        assert "x" in result
        assert "Int" in result


class TestLetBinding:
    """Tests for LetBinding factory function."""

    def test_let_binding_creation(self):
        """Test let binding creation."""
        let = LetBinding(
            var_binders=["x", "y"],
            let_terms=[Const("1", "Int"), Const("2", "Int")],
            subterms=[Expr("+", [Var("x", "Int"), Var("y", "Int")])]
        )
        assert let.kind == TermKind.LET_BINDING
        assert let.var_binders == ["x", "y"]

    def test_let_binding_str(self):
        """Test string representation of let binding."""
        let = LetBinding(
            var_binders=["x"],
            let_terms=[Const("1", "Int")],
            subterms=[Var("x", "Int")]
        )
        result = str(let)
        assert "(let" in result
        assert "x" in result


class TestLabeledTerm:
    """Tests for LabeledTerm factory function."""

    def test_labeled_term_creation(self):
        """Test labeled term creation."""
        inner = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        labeled = LabeledTerm((":named", "conj"), [inner])
        assert labeled.kind == TermKind.LABELED
        assert labeled.label == (":named", "conj")

    def test_labeled_term_str(self):
        """Test string representation of labeled term."""
        inner = Const("true", "Bool")
        labeled = LabeledTerm((":named", "label1"), [inner])
        result = str(labeled)
        assert "(!" in result
        assert ":named" in result
        assert "label1" in result


class TestHole:
    """Tests for Hole and hole functions."""

    def test_hole_creation(self):
        """Test hole creation."""
        hole = Hole(0)
        assert hole.kind == TermKind.HOLE

    def test_hole_name(self):
        """Test hole naming."""
        name = make_hole_name(5)
        assert name == "hole 5"

    def test_is_hole_function(self):
        """Test is_hole detection function."""
        hole = Hole(0)
        assert is_hole(hole) is True

        var = Var("x", "Int")
        assert is_hole(var) is False

    def test_hole_str(self):
        """Test string representation of hole."""
        hole = Hole(0)
        result = str(hole)
        assert "hole" in result


class TestTermClone:
    """Tests for Term.clone() method."""

    def test_clone_variable(self):
        """Test cloning a variable."""
        var = Var("x", "Int")
        cloned = var.clone()

        assert cloned.name == var.name
        assert cloned.type == var.type
        assert cloned is not var  # Different object

    def test_clone_expression(self):
        """Test cloning an expression."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        cloned = expr.clone()

        assert cloned.op == expr.op
        assert len(cloned.subterms) == len(expr.subterms)
        assert cloned is not expr

    def test_clone_deep_copy(self):
        """Test that clone is a deep copy."""
        inner = Var("x", "Int")
        expr = Expr(NOT, [inner])
        cloned = expr.clone()

        # Modify original
        inner.name = "y"

        # Clone should be unaffected
        assert cloned.subterms[0].name == "x"


class TestTermChildren:
    """Tests for Term.children() method."""

    def test_children_of_variable(self):
        """Test that variable has no children."""
        var = Var("x", "Int")
        children = list(var.children())
        assert len(children) == 0

    def test_children_of_expression(self):
        """Test children of expression."""
        a = Var("a", "Bool")
        b = Var("b", "Bool")
        expr = Expr(AND, [a, b])

        children = list(expr.children())
        assert len(children) == 2
        assert a in children
        assert b in children


class TestTermEquality:
    """Tests for Term equality."""

    def test_equal_variables(self):
        """Test that identical variables are equal."""
        v1 = Var("x", "Int")
        v2 = Var("x", "Int")
        assert v1 == v2

    def test_unequal_variables(self):
        """Test that different variables are not equal."""
        v1 = Var("x", "Int")
        v2 = Var("y", "Int")
        assert v1 != v2

    def test_equal_expressions(self):
        """Test that identical expressions are equal."""
        e1 = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        e2 = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        assert e1 == e2


class TestCommands:
    """Tests for SMT-LIB command classes."""

    def test_declare_const(self):
        """Test DeclareConst command."""
        cmd = DeclareConst("x", "Int")
        assert cmd.symbol == "x"
        assert cmd.sort == "Int"
        assert str(cmd) == "(declare-const x Int)"

    def test_declare_fun(self):
        """Test DeclareFun command."""
        cmd = DeclareFun("f", "Int Bool", "Int")
        assert cmd.symbol == "f"
        assert str(cmd) == "(declare-fun f (Int Bool) Int)"

    def test_assert(self):
        """Test Assert command."""
        term = Expr(">", [Var("x", "Int"), Const("0", "Int")])
        cmd = Assert(term)
        assert cmd.term == term
        assert "(assert" in str(cmd)

    def test_assert_soft(self):
        """Test AssertSoft command."""
        term = Var("x", "Bool")
        cmd = AssertSoft(term, [(":weight", "1")])
        assert "(assert-soft" in str(cmd)

    def test_define(self):
        """Test Define command."""
        term = Const("42", "Int")
        cmd = Define("meaning", term)
        assert cmd.symbol == "meaning"
        assert "(define" in str(cmd)

    def test_define_const(self):
        """Test DefineConst command."""
        cmd = DefineConst("true-val", "Bool", Const("true", "Bool"))
        assert cmd.symbol == "true-val"
        assert "(define-const" in str(cmd)

    def test_define_fun(self):
        """Test DefineFun command."""
        cmd = DefineFun("inc", "(x Int)", "Int", Expr("+", [Var("x", "Int"), Const("1", "Int")]))
        assert cmd.symbol == "inc"
        assert "(define-fun" in str(cmd)

    def test_check_sat(self):
        """Test CheckSat command."""
        cmd = CheckSat()
        assert str(cmd) == "(check-sat)"

    def test_check_sat_assuming(self):
        """Test CheckSatAssuming command."""
        cmd = CheckSatAssuming([Var("p", "Bool")])
        assert "(check-sat-assuming" in str(cmd)

    def test_push(self):
        """Test Push command."""
        assert str(Push()) == "(push)"
        assert str(Push([Const("2", "Int")])) == "(push 2)"

    def test_pop(self):
        """Test Pop command."""
        assert str(Pop()) == "(pop)"
        assert str(Pop([Const("1", "Int")])) == "(pop 1)"

    def test_get_value(self):
        """Test GetValue command."""
        cmd = GetValue([Var("x", "Int")])
        assert "(get-value" in str(cmd)

    def test_simplify(self):
        """Test Simplify command."""
        term = Var("x", "Int")
        cmd = Simplify(term, [])
        assert "(simplify" in str(cmd)

    def test_minimize(self):
        """Test Minimize command."""
        cmd = Minimize(Var("x", "Int"))
        assert "(minimize" in str(cmd)

    def test_maximize(self):
        """Test Maximize command."""
        cmd = Maximize(Var("x", "Int"))
        assert "(maximize" in str(cmd)

    def test_display(self):
        """Test Display command."""
        cmd = Display(Var("x", "Int"))
        assert "(display" in str(cmd)

    def test_eval(self):
        """Test Eval command."""
        cmd = Eval(Var("x", "Int"))
        assert "(eval" in str(cmd)

    def test_smtlib_command(self):
        """Test SMTLIBCommand catch-all."""
        cmd = SMTLIBCommand("(set-logic QF_LIA)")
        assert str(cmd) == "(set-logic QF_LIA)"


class TestScript:
    """Tests for Script class."""

    def test_script_creation(self):
        """Test basic script creation."""
        commands = [
            SMTLIBCommand("(set-logic QF_LIA)"),
            DeclareConst("x", "Int"),
            Assert(Expr(">", [Var("x", "Int"), Const("0", "Int")])),
            CheckSat(),
        ]
        script = Script(commands, {})

        assert len(script.commands) == 4
        assert len(script.assert_cmd) == 1

    def test_script_str(self):
        """Test script string representation."""
        commands = [DeclareConst("x", "Int"), CheckSat()]
        script = Script(commands, {})

        result = str(script)
        assert "declare-const" in result
        assert "check-sat" in result

    def test_script_vars_extraction(self):
        """Test variable extraction from script."""
        commands = [
            DeclareConst("x", "Int"),
            DeclareConst("y", "Bool"),
        ]
        script = Script(commands, {})

        assert len(script.vars) == 2
        var_names = [v.name for v in script.vars]
        assert "x" in var_names
        assert "y" in var_names

    def test_script_prefix_vars(self):
        """Test variable prefixing."""
        commands = [
            DeclareConst("x", "Int"),
            Assert(Expr(">", [Var("x", "Int"), Const("0", "Int")])),
        ]
        script = Script(commands, {"x": "Int"})

        script.prefix_vars("pre_")

        assert any("pre_x" in str(cmd) for cmd in script.commands)


class TestAstVisitorBase:
    """Tests for AstVisitorBase."""

    def test_visit_variable(self):
        """Test visiting a variable."""
        var = Var("x", "Int")
        visitor = AstVisitorBase()
        result = visitor.visit(var)
        assert result is None  # Default returns None

    def test_visit_expression(self):
        """Test visiting an expression."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        visitor = AstVisitorBase()
        result = visitor.visit(expr)
        assert result is None


class TestHoleCollector:
    """Tests for HoleCollector visitor."""

    def test_collect_holes(self):
        """Test collecting holes from expression."""
        hole0 = Hole(0)
        hole1 = Hole(1)
        expr = Expr(AND, [hole0, Expr(OR, [hole1, Const("true", "Bool")])])

        collector = HoleCollector()
        expr.accept(collector)

        assert len(collector.holes) == 2
        assert hole0 in collector.holes
        assert hole1 in collector.holes

    def test_no_holes(self):
        """Test expression with no holes."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])

        collector = HoleCollector()
        expr.accept(collector)

        assert len(collector.holes) == 0


class TestVariableCollector:
    """Tests for VariableCollector visitor."""

    def test_collect_variables(self):
        """Test collecting variables from expression."""
        a = Var("a", "Bool")
        b = Var("b", "Bool")
        c = Const("true", "Bool")
        expr = Expr(AND, [a, Expr(OR, [b, c])])

        collector = VariableCollector()
        expr.accept(collector)

        assert len(collector.variables) == 2
        assert a in collector.variables
        assert b in collector.variables
        assert c not in collector.variables  # Not a variable


class TestSubstitutionTransformer:
    """Tests for SubstitutionTransformer."""

    def test_substitute_variable(self):
        """Test substituting a variable."""
        old = Var("x", "Int")
        new = Var("y", "Int")
        expr = Expr("+", [old, Const("1", "Int")])

        transformer = SubstitutionTransformer(old, new)
        result = transformer.transform(expr)

        # Should have y instead of x
        result_str = str(result)
        assert "y" in result_str
        assert "x" not in result_str

    def test_substitute_no_match(self):
        """Test substitution when target not present."""
        old = Var("x", "Int")
        new = Var("y", "Int")
        expr = Expr("+", [Var("z", "Int"), Const("1", "Int")])

        transformer = SubstitutionTransformer(old, new)
        result = transformer.transform(expr)

        # Should be unchanged
        assert str(result) == str(expr)


class TestSkeletonExtractor:
    """Tests for SkeletonExtractor."""

    def test_extract_skeleton(self):
        """Test extracting skeleton from expression."""
        a = Var("a", "Bool")
        b = Var("b", "Bool")
        # (and a b) -> connectives preserved, vars become holes
        expr = Expr(AND, [a, b])

        extractor = SkeletonExtractor()
        skeleton = extractor.transform(expr)

        # Skeleton should have holes instead of variables
        assert skeleton.kind == TermKind.EXPRESSION
        # Check that children are holes
        children = list(skeleton.children())
        assert all(is_hole(c) for c in children)

    def test_extract_preserves_connectives(self):
        """Test that connectives are preserved during extraction."""
        a = Var("a", "Bool")
        expr = Expr(NOT, [Expr(OR, [a, Expr(AND, [Var("b", "Bool"), Var("c", "Bool")])])])

        extractor = SkeletonExtractor()
        skeleton = extractor.transform(expr)

        # Should still have NOT, OR, AND
        result_str = str(skeleton)
        assert "not" in result_str.lower() or NOT in result_str


class TestCollectBasicSubterms:
    """Tests for collect_basic_subterms function."""

    def test_collect_from_simple_expr(self):
        """Test collecting from simple expression."""
        expr = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        subterms, types = collect_basic_subterms(expr)

        # Should collect the variables (not the AND)
        assert len(subterms) == 2

    def test_collect_from_assert(self):
        """Test collecting from Assert command."""
        term = Expr(AND, [Var("a", "Bool"), Var("b", "Bool")])
        assertion = Assert(term)

        subterms, types = collect_basic_subterms(assertion)

        assert len(subterms) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
