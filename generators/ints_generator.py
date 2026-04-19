# complete Python module
import random
import string

# --- Constants and Configuration ---

_SMT_KEYWORDS = {
    # Core keywords and symbols
    "true", "false", "not", "and", "or", "xor", "=>", "ite", "let", "=", "distinct",
    "forall", "exists", "par",
    # Sort names
    "Bool", "Int", "Real", "Array", "String",
    # Command names
    "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-sort", "echo",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core",
    "get-value", "pop", "push", "reset", "reset-assertions", "set-info",
    "set-logic", "set-option",
    # Theory-specific function names from Ints and others
    "div", "mod", "abs", "divisible", "to_real", "to_int", "is_int",
    # Common operators that are technically not keywords but shouldn't be symbol names
    "<", "<=", ">", ">=", "+", "-", "*",
}

# --- Generation Parameters ---
_MAX_DEPTH = 5
_MAX_ARITY = 4
_MAX_LET_BINDINGS = 3
_MIN_VARS = 2
_MAX_VARS = 8
_NUMERAL_RANGE = (-100, 100)
_POS_NUMERAL_RANGE = (1, 100)
_SYMBOL_LEN = 6


class _FormulaGenerator:
    """Manages the state and generation of a single random SMT-LIB formula."""

    def __init__(self):
        self.used_names = set(_SMT_KEYWORDS)
        self.decls = []
        self.int_vars = []
        self.bool_vars = []
        self._initialize_declarations()

    def _new_symbol(self):
        """Generates a new, unique, valid SMT-LIB symbol name."""
        while True:
            # Generate a random string of lowercase letters
            name = ''.join(random.choices(string.ascii_lowercase, k=_SYMBOL_LEN))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _initialize_declarations(self):
        """Creates initial (declare-const ...) for Int and Bool variables."""
        num_int_vars = random.randint(_MIN_VARS, _MAX_VARS)
        num_bool_vars = random.randint(_MIN_VARS, _MAX_VARS)

        for _ in range(num_int_vars):
            name = self._new_symbol()
            self.int_vars.append(name)
            self.decls.append(f"(declare-const {name} Int)")

        for _ in range(num_bool_vars):
            name = self._new_symbol()
            self.bool_vars.append(name)
            self.decls.append(f"(declare-const {name} Bool)")

    # --- Terminal and Helper Generators ---

    def _generate_signed_numeral(self):
        val = random.randint(*_NUMERAL_RANGE)
        return f"(- {-val})" if val < 0 else str(val)

    def _generate_positive_numeral(self):
        return str(random.randint(*_POS_NUMERAL_RANGE))

    # --- Main Recursive Term Generators ---

    def _generate_int_term(self, depth):
        if depth >= _MAX_DEPTH:
            if self.int_vars and random.random() < 0.75:
                return random.choice(self.int_vars)
            return self._generate_signed_numeral()

        productions = [
            self._gen_int_terminal, self._gen_int_unary_minus, self._gen_int_n_ary_op,
            self._gen_int_mod, self._gen_int_abs, self._gen_int_ite, self._gen_int_let,
        ]
        # At shallow depths, encourage complex structures. At deep depths, force terminals.
        weights = [10, 2, 8, 3, 2, 6, 4] if depth < _MAX_DEPTH - 1 else [10, 1, 0, 0, 0, 0, 0]
        chosen_production = random.choices(productions, weights=weights, k=1)[0]
        return chosen_production(depth)

    def _generate_bool_term(self, depth):
        if depth >= _MAX_DEPTH:
            if self.bool_vars and random.random() < 0.75:
                return random.choice(self.bool_vars)
            return random.choice(["true", "false"])

        productions = [
            self._gen_bool_terminal, self._gen_bool_not, self._gen_bool_n_ary_op,
            self._gen_bool_eq_distinct, self._gen_bool_ite, self._gen_bool_let,
            self._gen_bool_int_relation, self._gen_bool_divisible,
        ]
        weights = [10, 4, 10, 8, 6, 5, 10, 2] if depth < _MAX_DEPTH - 1 else [10, 1, 0, 0, 0, 0, 0, 0]
        chosen_production = random.choices(productions, weights=weights, k=1)[0]
        return chosen_production(depth)

    # --- Integer Term Production Implementations ---

    def _gen_int_terminal(self, depth):
        if self.int_vars:
            return random.choice([random.choice(self.int_vars), self._generate_signed_numeral()])
        return self._generate_signed_numeral()

    def _gen_int_unary_minus(self, depth):
        arg = self._generate_int_term(depth + 1)
        return f"(- {arg})"

    def _gen_int_n_ary_op(self, depth):
        op = random.choice(["+", "-", "*", "div"])
        arity = random.randint(2, _MAX_ARITY)
        args = [self._generate_int_term(depth + 1) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_int_mod(self, depth):
        arg1 = self._generate_int_term(depth + 1)
        arg2 = self._generate_int_term(depth + 1)
        return f"(mod {arg1} {arg2})"

    def _gen_int_abs(self, depth):
        arg = self._generate_int_term(depth + 1)
        return f"(abs {arg})"

    def _gen_int_ite(self, depth):
        cond = self._generate_bool_term(depth + 1)
        then_b = self._generate_int_term(depth + 1)
        else_b = self._generate_int_term(depth + 1)
        return f"(ite {cond} {then_b} {else_b})"

    def _gen_int_let(self, depth):
        return self._generate_let_binding(depth, 'Int')

    # --- Boolean Term Production Implementations ---

    def _gen_bool_terminal(self, depth):
        options = ["true", "false"]
        if self.bool_vars:
            options.extend(self.bool_vars)
        return random.choice(options)

    def _gen_bool_not(self, depth):
        arg = self._generate_bool_term(depth + 1)
        return f"(not {arg})"

    def _gen_bool_n_ary_op(self, depth):
        op = random.choice(["and", "or", "=>", "xor"])
        arity = random.randint(2, _MAX_ARITY)
        args = [self._generate_bool_term(depth + 1) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_bool_eq_distinct(self, depth):
        op = random.choice(["=", "distinct"])
        arity = random.randint(2, _MAX_ARITY)
        if random.choice([True, False]):  # Compare Ints
            args = [self._generate_int_term(depth + 1) for _ in range(arity)]
        else:  # Compare Bools
            args = [self._generate_bool_term(depth + 1) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_bool_ite(self, depth):
        cond = self._generate_bool_term(depth + 1)
        then_b = self._generate_bool_term(depth + 1)
        else_b = self._generate_bool_term(depth + 1)
        return f"(ite {cond} {then_b} {else_b})"

    def _gen_bool_let(self, depth):
        return self._generate_let_binding(depth, 'Bool')

    def _gen_bool_int_relation(self, depth):
        op = random.choice(["<=", "<", ">=", ">"])
        arity = random.randint(2, _MAX_ARITY)
        args = [self._generate_int_term(depth + 1) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _gen_bool_divisible(self, depth):
        k = self._generate_positive_numeral()
        arg = self._generate_int_term(depth + 1)
        return f"((_ divisible {k}) {arg})"

    # --- Let Binding Helper ---

    def _generate_let_binding(self, depth, return_sort):
        num_bindings = random.randint(1, _MAX_LET_BINDINGS)
        bindings = []
        new_vars_to_add = []  # list of (name, sort) tuples

        # Phase 1: Generate all binding terms without modifying the current scope.
        # This correctly models the parallel binding semantics of `let`.
        for _ in range(num_bindings):
            var_name = self._new_symbol()
            if random.choice([True, False]):  # Int binding
                term = self._generate_int_term(depth + 1)
                bindings.append(f"({var_name} {term})")
                new_vars_to_add.append((var_name, 'Int'))
            else:  # Bool binding
                term = self._generate_bool_term(depth + 1)
                bindings.append(f"({var_name} {term})")
                new_vars_to_add.append((var_name, 'Bool'))
        
        new_int_vars = [name for name, sort in new_vars_to_add if sort == 'Int']
        new_bool_vars = [name for name, sort in new_vars_to_add if sort == 'Bool']

        try:
            # Phase 2: Add the new variables to the scope so they are visible in the body.
            self.int_vars.extend(new_int_vars)
            self.bool_vars.extend(new_bool_vars)

            # Phase 3: Generate the body of the `let` expression.
            if return_sort == 'Int':
                body = self._generate_int_term(depth + 1)
            else:  # 'Bool'
                body = self._generate_bool_term(depth + 1)

            bindings_str = ' '.join(bindings)
            return f"(let ({bindings_str}) {body})"
        finally:
            # Phase 4: Clean up the scope by removing the temporary let-bound variables.
            if new_int_vars:
                self.int_vars = self.int_vars[:-len(new_int_vars)]
            if new_bool_vars:
                self.bool_vars = self.bool_vars[:-len(new_bool_vars)]


def generate_ints_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB formula in the Ints theory.

    This function implements a random formula generator based on a context-free
    grammar for SMT-LIB's `Ints` theory. It prioritizes diversity in the
    generated terms by varying operators, term shapes, nesting patterns, and
    the number of variables.

    The generated formula is a single Boolean term, and all symbols used within
    it are declared. The output is suitable for fuzzing or testing SMT solvers.

    Returns:
        tuple[str, str]: A tuple where the first element is a string of
        SMT-LIB declarations (e.g., `(declare-const ...)`), and the second
        element is a string representing the generated Boolean term.
    """
    generator = _FormulaGenerator()
    formula_str = generator._generate_bool_term(depth=0)
    decls_str = "\n".join(generator.decls)
    return decls_str, formula_str