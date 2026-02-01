# complete Python module
import random
import string

# SMT-LIB keywords and reserved words to avoid for symbol names.
# This is not exhaustive but covers the most common ones.
_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false",
    "assert", "check-sat", "declare-const", "declare-fun", "define-fun",
    "get-value", "get-model", "exit", "set-logic", "set-option",
    "forall", "exists", "let",
    "=", "distinct", "<", "<=", ">", ">=",
    "+", "-", "*", "/",
    "sin", "cos", "tan", "csc", "sec", "cot",
    "arcsin", "arccos", "arctan", "arccsc", "arcsec", "arccot",
    "exp", "sqrt", "real.pi",
    "Bool", "Real", "Int", "Array", "BitVec",
}

# Operator sets based on the provided CFG.
_RELATION_OPS = ["<", "<=", ">", ">="]
_ARITHMETIC_OPS = ["+", "-", "*", "/"]
_TRANSCENDENTAL_OPS = [
    "sqrt", "exp", "sin", "cos", "tan", "csc", "sec", "cot",
    "arcsin", "arccos", "arctan", "arccsc", "arcsec", "arccot"
]
_BOOL_CONNECTIVES = ["and", "or", "xor", "=>"]


class _FormulaGenerator:
    """
    A stateful generator for a single random SMT-LIB formula.
    This class encapsulates the state, such as declared variables and recursion depth,
    for one generation task.
    """

    def __init__(self):
        # Configuration for the generation process
        self.max_depth = random.randint(4, 7)
        self.max_real_vars = random.randint(2, 6)
        self.max_bool_vars = random.randint(2, 6)
        self.max_nary_operands = 4

        # State for the current formula
        self.real_vars = []
        self.bool_vars = []
        self.decls = []
        self.used_names = set(_SMT_KEYWORDS)

    def _generate_unique_name(self, length=5):
        """Generates a random, unique, valid SMT-LIB symbol name."""
        chars = string.ascii_lowercase
        while True:
            name = "".join(random.choice(chars) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _generate_symbol(self, sort):
        """
        Generates a symbol of a given sort.
        It may create a new variable or reuse an existing one.
        """
        target_vars = self.real_vars if sort == 'Real' else self.bool_vars
        max_vars = self.max_real_vars if sort == 'Real' else self.max_bool_vars

        # Decide whether to create a new variable.
        # We must create one if none exist for the sort.
        # Otherwise, create one with a certain probability if we are under the limit.
        should_create_new = not target_vars or \
                            (len(target_vars) < max_vars and random.random() < 0.2)

        if should_create_new:
            name = self._generate_unique_name()
            self.decls.append(f"(declare-const {name} {sort})")
            target_vars.append(name)
            return name
        else:
            return random.choice(target_vars)

    def _generate_numeral(self):
        """Generates a random SMT-LIB numeral for the Reals sort."""
        forms = ['int', 'decimal', 'rational']
        chosen_form = random.choice(forms)

        if chosen_form == 'int':
            return str(random.randint(-100, 100))
        elif chosen_form == 'decimal':
            val = random.uniform(-100.0, 100.0)
            # Format to ensure it has a decimal point, e.g., 5.0 not 5.
            s_val = f"{val:.4f}".rstrip('0')
            if s_val.endswith('.'):
                s_val += '0'
            return s_val if s_val not in ('0', '-0') else '0.0'
        else:  # rational
            num = random.randint(1, 50)
            den = random.randint(1, 50)
            if random.random() < 0.5:
                return f"(/ (- {num}) {den})"
            return f"(/ {num} {den})"

    def _generate_real_term(self, depth):
        """Generates a term of sort Real, following the <real_term> CFG rule."""
        if depth >= self.max_depth:
            # Base case: terminate recursion with a non-recursive element.
            productions = ['symbol', 'numeral', 'pi']
            weights = [0.6, 0.3, 0.1]
        else:
            productions = ['symbol', 'numeral', 'pi', 'arithmetic', 'transcendental']
            weights = [0.15, 0.1, 0.05, 0.35, 0.35]

        choice = random.choices(productions, weights=weights)[0]

        if choice == 'symbol':
            return self._generate_symbol('Real')
        elif choice == 'numeral':
            return self._generate_numeral()
        elif choice == 'pi':
            return "real.pi"
        elif choice == 'arithmetic':
            op = random.choice(_ARITHMETIC_OPS)
            # The CFG allows one or more operands for all arithmetic ops.
            # We generate unary minus with some probability, otherwise n-ary.
            if op == '-' and random.random() < 0.3:
                arity = 1
            else:
                arity = random.randint(2, self.max_nary_operands)
            
            args = [self._generate_real_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"
        else:  # transcendental
            op = random.choice(_TRANSCENDENTAL_OPS)
            arg = self._generate_real_term(depth + 1)
            return f"({op} {arg})"

    def _generate_predicate(self, depth):
        """Generates a predicate, following the <predicate> CFG rule."""
        productions = ['relation', 'equality']
        weights = [0.7, 0.3]
        choice = random.choices(productions, weights=weights)[0]

        if choice == 'relation':
            op = random.choice(_RELATION_OPS)
            arg1 = self._generate_real_term(depth + 1)
            arg2 = self._generate_real_term(depth + 1)
            return f"({op} {arg1} {arg2})"
        else:  # equality
            op = random.choice(["=", "distinct"])
            arity = random.randint(2, self.max_nary_operands)
            args = [self._generate_real_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"

    def _generate_bool_term(self, depth):
        """Generates a term of sort Bool, following the <bool_term> CFG rule."""
        if depth >= self.max_depth:
            productions = ['symbol', 'literal']
            weights = [0.7, 0.3]
        else:
            productions = ['symbol', 'literal', 'predicate', 'not', 'connective', 'ite']
            weights = [0.1, 0.05, 0.3, 0.15, 0.25, 0.15]

        choice = random.choices(productions, weights=weights)[0]

        if choice == 'symbol':
            return self._generate_symbol('Bool')
        elif choice == 'literal':
            return random.choice(["true", "false"])
        elif choice == 'predicate':
            return self._generate_predicate(depth + 1)
        elif choice == 'not':
            arg = self._generate_bool_term(depth + 1)
            return f"(not {arg})"
        elif choice == 'connective':
            op = random.choice(_BOOL_CONNECTIVES)
            arity = random.randint(2, self.max_nary_operands)
            args = [self._generate_bool_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"
        else:  # ite
            cond = self._generate_bool_term(depth + 1)
            then_b = self._generate_bool_term(depth + 1)
            else_b = self._generate_bool_term(depth + 1)
            return f"(ite {cond} {then_b} {else_b})"

    def generate_formula(self):
        """The main entry point to generate a complete Boolean formula."""
        return self._generate_bool_term(0)


def generate_transcendentals_formula_with_decls():
    """
    Generates a random, well-formed SMT-LIB formula for the theory of
    transcendentals (QF_NRAT), following a specific CFG.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): A newline-separated string of SMT-LIB declarations
          for all symbols used in the formula.
        - formula (str): A single SMT-LIB Boolean term representing the
          randomly generated formula.
    """
    generator = _FormulaGenerator()
    formula_str = generator.generate_formula()
    
    # Sort declarations for deterministic output given a seed
    sorted_decls = sorted(generator.decls)
    decls_str = "\n".join(sorted_decls)
    
    return decls_str, formula_str