# complete Python module
import random
import string

# A set of SMT-LIB keywords and function names to avoid for generated symbols.
_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "exists", "forall",
    "let", "assert", "check-sat", "declare-const", "declare-fun", "define-fun",
    "get-value", "get-model", "exit", "set-logic", "Int", "Bool", "Unicode",
    "char.<=", "char.is_digit", "char.to_int", "_", "Char",
    "<", "<=", ">", ">="
}

def _generate_random_name(used_names):
    """
    Generates a random, valid, and unused SMT-LIB symbol name.
    A valid name is >= 5 characters, lowercase ASCII, and not a keyword.
    """
    while True:
        length = random.randint(5, 10)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in used_names:
            used_names.add(name)
            return name

class _FormulaGenerator:
    """
    Encapsulates the state and logic for generating a single random formula
    based on the z3_characters CFG. This class is intended for internal use
    by the public API function.
    """
    def __init__(self):
        self.max_depth = random.randint(3, 6)
        self.used_names = set(_SMT_KEYWORDS)
        self.declarations = []
        self.unicode_vars = []
        self.int_vars = []

        self._declare_variables()

    def _declare_variables(self):
        """Declares a random number of variables for Int and Unicode sorts."""
        num_unicode_vars = random.randint(1, 4)
        for _ in range(num_unicode_vars):
            name = _generate_random_name(self.used_names)
            self.unicode_vars.append(name)
            self.declarations.append(f"(declare-const {name} Unicode)")

        num_int_vars = random.randint(1, 4)
        for _ in range(num_int_vars):
            name = _generate_random_name(self.used_names)
            self.int_vars.append(name)
            self.declarations.append(f"(declare-const {name} Int)")

    def generate(self):
        """Generates the full formula and returns declarations and the term."""
        formula = self._generate_bool_term(0)
        decls_str = "\n".join(self.declarations)
        return decls_str, formula

    # --- Term Generation Methods (corresponding to CFG non-terminals) ---

    def _generate_bool_term(self, depth):
        if depth >= self.max_depth:
            return random.choice(["true", "false"])

        # At depth 0, we must generate a predicate to avoid trivial "true" formulas.
        if depth == 0:
            return self._generate_predicate(depth + 1)

        # At deeper levels, allow terminals but bias towards complex predicates.
        choices = [self._generate_predicate, lambda d: "true", lambda d: "false"]
        weights = [0.85, 0.075, 0.075]
        chosen_generator = random.choices(choices, weights=weights, k=1)[0]
        return chosen_generator(depth + 1)

    def _generate_predicate(self, depth):
        # List of functions that generate specific predicate forms.
        predicate_generators = [
            self._gen_char_le,
            self._gen_char_is_digit,
            self._gen_logic_op,
            self._gen_not,
            self._gen_relation_op,
            self._gen_eq,
        ]
        chosen_generator = random.choice(predicate_generators)
        return chosen_generator(depth)

    def _generate_unicode_term(self, depth):
        # Options: use a variable or a literal `(_ Char numeral)`
        # If no variables are declared, must use a literal.
        use_var_possible = self.unicode_vars and depth < self.max_depth

        if use_var_possible and random.random() < 0.7: # Bias towards variables
            return random.choice(self.unicode_vars)
        else: # Generate a literal
            # Bias towards common ASCII for more interesting interactions
            if random.random() < 0.8:
                numeral = random.randint(32, 126) # Printable ASCII
            else:
                numeral = random.randint(0, 255) # Latin-1
            return f"(_ Char {numeral})"

    def _generate_int_term(self, depth):
        if depth >= self.max_depth:
            # At max depth, choose from terminals: literal or variable.
            if self.int_vars and random.random() < 0.5:
                return random.choice(self.int_vars)
            return str(random.randint(0, 255))

        # Options: variable, literal, or `(char.to_int ...)`
        # Create a weighted list of possible generators.
        generators, weights = [], []
        if self.int_vars:
            generators.append(lambda: random.choice(self.int_vars))
            weights.append(0.4)
        
        generators.append(lambda: f"(char.to_int {self._generate_unicode_term(depth + 1)})")
        weights.append(0.4)

        generators.append(lambda: str(random.randint(0, 500)))
        weights.append(0.2)
        
        chosen_generator = random.choices(generators, weights=weights, k=1)[0]
        return chosen_generator()

    def _generate_term_for_eq(self, depth):
        """
        Helper for '=' predicate. Chooses a sort, then generates two
        terms of that same sort to ensure well-typedness.
        """
        sort = random.choice(["Bool", "Unicode", "Int"])
        if sort == "Bool":
            term1 = self._generate_bool_term(depth + 1)
            term2 = self._generate_bool_term(depth + 1)
        elif sort == "Unicode":
            term1 = self._generate_unicode_term(depth + 1)
            term2 = self._generate_unicode_term(depth + 1)
        else: # Int
            term1 = self._generate_int_term(depth + 1)
            term2 = self._generate_int_term(depth + 1)
        return term1, term2

    # --- Predicate Implementation Helpers ---

    def _gen_char_le(self, depth):
        term1 = self._generate_unicode_term(depth + 1)
        term2 = self._generate_unicode_term(depth + 1)
        return f"(char.<= {term1} {term2})"

    def _gen_char_is_digit(self, depth):
        term = self._generate_unicode_term(depth + 1)
        return f"(char.is_digit {term})"

    def _gen_logic_op(self, depth):
        op = random.choice(["and", "or", "xor", "=>"])
        # SMT-LIB logic ops take 2 or more arguments (for and, or, xor).
        num_args = random.randint(2, 4)
        args = [self._generate_bool_term(depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"

    def _gen_not(self, depth):
        arg = self._generate_bool_term(depth + 1)
        return f"(not {arg})"

    def _gen_relation_op(self, depth):
        op = random.choice(["<", "<=", ">", ">="])
        term1 = self._generate_int_term(depth + 1)
        term2 = self._generate_int_term(depth + 1)
        return f"({op} {term1} {term2})"

    def _gen_eq(self, depth):
        term1, term2 = self._generate_term_for_eq(depth)
        return f"(= {term1} {term2})"


def generate_z3characters_formula_with_decls():
    """
    Generates a random, well-formed SMT-LIB2 formula for the z3_characters
    theory, strictly following the specified CFG.

    This function creates a random context (variables, constants) and then
    recursively builds a formula term. The process is randomized to ensure
    diversity in the output, covering different operators, term shapes, and
    nesting patterns.

    Returns:
        A tuple (decls, formula), where:
        - decls (str): A string of SMT-LIB2 `(declare-const ...)` statements
          for all generated symbols, separated by newlines.
        - formula (str): A single SMT-LIB2 Boolean term representing the
          randomly generated formula.
    """
    generator = _FormulaGenerator()
    return generator.generate()