# complete Python module
from __future__ import annotations

import random
import string

# A set of SMT-LIB keywords and function names to avoid when generating random symbols.
# This prevents generating syntactically invalid formulas like (declare-const and Bool).
_SMT_KEYWORDS = {
    "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-sort", "echo",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-core", "get-value", "pop", "push",
    "reset", "reset-assertions", "set-info", "set-logic", "set-option",
    "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct", "ite",
    "forall", "exists", "let", "Int", "Real", "Bool", "to_real", "to_int",
    "is_int", "div", "mod", "abs", "divisible", "+", "-", "*", "/", "<=", "<",
    ">=", ">", "as", "BINARY", "DECIMAL", "exists", "forall", "HEXADECIMAL",
    "let", "match", "NUMERAL", "par", "STRING"
}

# Sorts used in the Reals_Ints logic.
_SORTS = ["Int", "Real", "Bool"]


class _FormulaGenerator:
    """
    A stateful class to generate a random SMT-LIB formula for the Reals_Ints theory.
    This class is not part of the public API and is prefixed with an underscore.
    """

    def __init__(self, max_depth=6, initial_vars=4):
        self.max_depth = max_depth
        self.initial_vars = initial_vars
        self.used_names = set(_SMT_KEYWORDS)
        self.decls = []

    def _generate_symbol_name(self) -> str:
        """Generates a new, unique symbol name."""
        while True:
            length = random.randint(5, 10)
            name = ''.join(random.choices(string.ascii_lowercase, k=length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _add_decl(self, name: str, sort: str):
        """Adds a (declare-const ...) to the list of declarations."""
        self.decls.append(f"(declare-const {name} {sort})")

    def _get_vars_of_sort(self, sort: str, scope: dict) -> list[str]:
        """Returns a list of all variables of a given sort in the current scope."""
        return [name for name, s in scope.items() if s == sort]

    def _get_or_create_var(self, sort: str, scope: dict) -> str:
        """
        Retrieves a random existing variable of the given sort from the scope.
        If none exist, it creates, declares, and adds a new one to the scope.
        """
        candidates = self._get_vars_of_sort(sort, scope)
        if candidates and random.random() < 0.8:
            return random.choice(candidates)
        
        # Create a new variable
        name = self._generate_symbol_name()
        scope[name] = sort
        self._add_decl(name, sort)
        return name

    def _generate_numeral(self) -> str:
        """Generates a string for an integer literal."""
        return str(random.randint(-1000, 1000))

    def _generate_positive_numeral(self) -> str:
        """Generates a string for a positive integer literal (> 0)."""
        return str(random.randint(1, 100))

    def _generate_decimal(self) -> str:
        """Generates a string for a real literal."""
        val = random.uniform(-1000.0, 1000.0)
        # SMT-LIB requires at least one digit after the decimal point for reals
        return f"{val:.4f}"

    def _is_terminal_depth(self, depth: int) -> bool:
        """
        Decides if generation should stop recursing and produce a terminal.
        The probability of stopping increases with depth.
        """
        if depth >= self.max_depth:
            return True
        # Increase probability of terminating as depth increases
        prob_terminate = (depth / self.max_depth) ** 2
        return random.random() < prob_terminate

    # -----------------------------------------------------------------
    # <bool_term> Productions
    # -----------------------------------------------------------------

    def _generate_bool_term(self, depth: int, scope: dict) -> str:
        """Generates a term of sort Bool, following the CFG."""
        if self._is_terminal_depth(depth):
            # Terminal productions for <bool_term>
            terminals = [
                lambda: "true",
                lambda: "false",
                lambda: self._get_or_create_var("Bool", scope)
            ]
            return random.choice(terminals)()

        # Non-terminal productions for <bool_term>
        productions = [
            self._gen_bool_not, self._gen_bool_nary_connective,
            self._gen_bool_equality, self._gen_bool_distinct,
            self._gen_bool_ite, self._gen_relation, self._gen_is_int,
            self._gen_divisible, self._gen_binder, self._gen_let
        ]
        # Give binders a slightly lower chance to avoid overly complex formulas
        weights = [10, 15, 12, 12, 10, 15, 5, 3, 4, 4]
        chosen_prod = random.choices(productions, weights=weights, k=1)[0]
        return chosen_prod(depth, scope)

    def _gen_bool_not(self, depth: int, scope: dict) -> str:
        arg = self._generate_bool_term(depth + 1, scope)
        return f"(not {arg})"

    def _gen_bool_nary_connective(self, depth: int, scope: dict) -> str:
        op = random.choice(["and", "or", "xor", "=>"])
        arity = random.randint(2, 4)
        args = [self._generate_bool_term(depth + 1, scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_bool_equality(self, depth: int, scope: dict) -> str:
        sort = random.choice(_SORTS)
        if sort == "Int":
            arg1 = self._generate_int_term(depth + 1, scope)
            arg2 = self._generate_int_term(depth + 1, scope)
        elif sort == "Real":
            arg1 = self._generate_real_term(depth + 1, scope)
            arg2 = self._generate_real_term(depth + 1, scope)
        else:  # Bool
            arg1 = self._generate_bool_term(depth + 1, scope)
            arg2 = self._generate_bool_term(depth + 1, scope)
        return f"(= {arg1} {arg2})"

    def _gen_bool_distinct(self, depth: int, scope: dict) -> str:
        sort = random.choice(_SORTS)
        arity = random.randint(2, 4)
        if sort == "Int":
            args = [self._generate_int_term(depth + 1, scope) for _ in range(arity)]
        elif sort == "Real":
            args = [self._generate_real_term(depth + 1, scope) for _ in range(arity)]
        else:  # Bool
            args = [self._generate_bool_term(depth + 1, scope) for _ in range(arity)]
        return f"(distinct {' '.join(args)})"

    def _gen_bool_ite(self, depth: int, scope: dict) -> str:
        cond = self._generate_bool_term(depth + 1, scope)
        then_b = self._generate_bool_term(depth + 1, scope)
        else_b = self._generate_bool_term(depth + 1, scope)
        return f"(ite {cond} {then_b} {else_b})"

    def _gen_relation(self, depth: int, scope: dict) -> str:
        op = random.choice(["<=", "<", ">=", ">"])
        sort = random.choice(["Int", "Real"])
        arity = random.randint(2, 4)
        if sort == "Int":
            args = [self._generate_int_term(depth + 1, scope) for _ in range(arity)]
        else:  # Real
            args = [self._generate_real_term(depth + 1, scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_is_int(self, depth: int, scope: dict) -> str:
        arg = self._generate_real_term(depth + 1, scope)
        return f"(is_int {arg})"

    def _gen_divisible(self, depth: int, scope: dict) -> str:
        k = self._generate_positive_numeral()
        arg = self._generate_int_term(depth + 1, scope)
        return f"((_ divisible {k}) {arg})"

    def _gen_binder(self, depth: int, scope: dict) -> str:
        binder = random.choice(["forall", "exists"])
        num_vars = random.randint(1, 3)
        new_scope = scope.copy()
        sorted_vars_str = []
        for _ in range(num_vars):
            var_name = self._generate_symbol_name()
            var_sort = random.choice(_SORTS)
            new_scope[var_name] = var_sort
            sorted_vars_str.append(f"({var_name} {var_sort})")
        
        vars_list_str = " ".join(sorted_vars_str)
        body = self._generate_bool_term(depth + 1, new_scope)
        return f"({binder} ({vars_list_str}) {body})"

    def _gen_let(self, depth: int, scope: dict, sort_out: str = "Bool") -> str:
        num_bindings = random.randint(1, 3)
        
        bindings_info = []
        binding_strs = []
        # Generate binding values using the current scope
        for _ in range(num_bindings):
            var_name = self._generate_symbol_name()
            var_sort = random.choice(_SORTS)
            
            if var_sort == "Int":
                value_term = self._generate_int_term(depth + 1, scope)
            elif var_sort == "Real":
                value_term = self._generate_real_term(depth + 1, scope)
            else: # Bool
                value_term = self._generate_bool_term(depth + 1, scope)
            
            bindings_info.append((var_name, var_sort))
            binding_strs.append(f"({var_name} {value_term})")

        # Create new scope for the body
        new_scope = scope.copy()
        for var_name, var_sort in bindings_info:
            new_scope[var_name] = var_sort
            
        binding_list_str = " ".join(binding_strs)
        
        # Generate body using the new scope
        if sort_out == "Bool":
            body = self._generate_bool_term(depth + 1, new_scope)
        elif sort_out == "Int":
            body = self._generate_int_term(depth + 1, new_scope)
        else: # Real
            body = self._generate_real_term(depth + 1, new_scope)
            
        return f"(let ({binding_list_str}) {body})"

    # -----------------------------------------------------------------
    # <int_term> Productions
    # -----------------------------------------------------------------

    def _generate_int_term(self, depth: int, scope: dict) -> str:
        """Generates a term of sort Int, following the CFG."""
        if self._is_terminal_depth(depth):
            terminals = [
                self._generate_numeral,
                lambda: self._get_or_create_var("Int", scope)
            ]
            return random.choice(terminals)()

        productions = [
            self._gen_int_unary_minus, self._gen_int_nary_op,
            self._gen_int_mod, self._gen_int_abs, self._gen_to_int,
            self._gen_int_ite,
            lambda d, s: self._gen_let(d, s, sort_out="Int")
        ]
        weights = [10, 25, 10, 10, 10, 15, 5]
        chosen_prod = random.choices(productions, weights=weights, k=1)[0]
        return chosen_prod(depth, scope)

    def _gen_int_unary_minus(self, depth: int, scope: dict) -> str:
        return f"(- {self._generate_int_term(depth + 1, scope)})"

    def _gen_int_nary_op(self, depth: int, scope: dict) -> str:
        op = random.choice(["+", "-", "*", "div"])
        arity = random.randint(2, 4)
        args = [self._generate_int_term(depth + 1, scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_int_mod(self, depth: int, scope: dict) -> str:
        arg1 = self._generate_int_term(depth + 1, scope)
        arg2 = self._generate_int_term(depth + 1, scope)
        return f"(mod {arg1} {arg2})"

    def _gen_int_abs(self, depth: int, scope: dict) -> str:
        return f"(abs {self._generate_int_term(depth + 1, scope)})"

    def _gen_to_int(self, depth: int, scope: dict) -> str:
        return f"(to_int {self._generate_real_term(depth + 1, scope)})"

    def _gen_int_ite(self, depth: int, scope: dict) -> str:
        cond = self._generate_bool_term(depth + 1, scope)
        then_b = self._generate_int_term(depth + 1, scope)
        else_b = self._generate_int_term(depth + 1, scope)
        return f"(ite {cond} {then_b} {else_b})"

    # -----------------------------------------------------------------
    # <real_term> Productions
    # -----------------------------------------------------------------

    def _generate_real_term(self, depth: int, scope: dict) -> str:
        """Generates a term of sort Real, following the CFG."""
        if self._is_terminal_depth(depth):
            terminals = [
                self._generate_decimal,
                lambda: self._get_or_create_var("Real", scope)
            ]
            return random.choice(terminals)()

        productions = [
            self._gen_real_unary_minus, self._gen_real_nary_op,
            self._gen_to_real, self._gen_real_ite,
            lambda d, s: self._gen_let(d, s, sort_out="Real")
        ]
        weights = [15, 35, 15, 20, 5]
        chosen_prod = random.choices(productions, weights=weights, k=1)[0]
        return chosen_prod(depth, scope)

    def _gen_real_unary_minus(self, depth: int, scope: dict) -> str:
        return f"(- {self._generate_real_term(depth + 1, scope)})"

    def _gen_real_nary_op(self, depth: int, scope: dict) -> str:
        op = random.choice(["+", "-", "*", "/"])
        arity = random.randint(2, 4)
        args = [self._generate_real_term(depth + 1, scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_to_real(self, depth: int, scope: dict) -> str:
        return f"(to_real {self._generate_int_term(depth + 1, scope)})"

    def _gen_real_ite(self, depth: int, scope: dict) -> str:
        cond = self._generate_bool_term(depth + 1, scope)
        then_b = self._generate_real_term(depth + 1, scope)
        else_b = self._generate_real_term(depth + 1, scope)
        return f"(ite {cond} {then_b} {else_b})"

    # -----------------------------------------------------------------
    # Main generation entry point
    # -----------------------------------------------------------------

    def generate(self) -> tuple[str, str]:
        """
        Generates and returns a tuple of (declarations, formula_string).
        """
        initial_scope = {}
        # Pre-populate with some initial variables to ensure terminals are available
        for _ in range(self.initial_vars):
            sort = random.choice(_SORTS)
            self._get_or_create_var(sort, initial_scope)

        # Generate the main formula, starting at depth 0
        formula = self._generate_bool_term(0, initial_scope)

        # Format declarations
        decls_str = "\n".join(sorted(list(set(self.decls))))

        return decls_str, formula


def generate_realsints_formula_with_decls() -> tuple[str, str]:
    """
    Generates a random, well-typed SMT-LIB2 formula for the Reals_Ints theory.

    This function implements a random formula generator based on a context-free
    grammar for Boolean terms in the Reals_Ints theory. It prioritizes diversity
    in the generated formulas by randomly selecting operators, term structures,
    and nesting patterns.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): A string containing all necessary SMT-LIB2
          `(declare-const ...)` declarations for the symbols used in the formula.
        - formula (str): A string representing a single, well-typed Boolean term.
    """
    max_depth = random.randint(5, 8)
    initial_vars = random.randint(3, 6)
    generator = _FormulaGenerator(max_depth=max_depth, initial_vars=initial_vars)
    return generator.generate()