# complete Python module
import random
import string

class _CVC5StringsFormulaGenerator:
    """
    A helper class that encapsulates the state and logic for generating a single
    random SMT-LIB formula based on the cvc5_Strings CFG. An instance of this
    class is created for each call to the public generation function.
    """

    # A set of SMT-LIB keywords to avoid for generated symbol names.
    _KEYWORDS = {
        # Core Commands
        "declare-sort", "define-sort", "declare-const", "declare-fun", "define-fun",
        "assert", "check-sat", "get-model", "exit", "set-logic", "set-option",
        "get-value", "get-info", "echo", "push", "pop",
        # Core Sorts & Values
        "Bool", "Int", "String", "RegLan", "true", "false",
        # Core Operators
        "not", "and", "or", "xor", "=>", "ite", "=", "distinct",
        "+", "-", "*", "div", "mod", "abs", "<", "<=", ">", ">=",
        # String Theory
        "str.++", "str.at", "str.substr", "str.replace", "str.replace_all",
        "str.replace_re", "str.replace_re_all", "str.from_int", "str.from_code",
        "str.len", "str.to_int", "str.to_code", "str.indexof", "str.<",
        "str.<=", "str.prefixof", "str.suffixof", "str.contains", "str.is_digit",
        "str.in_re", "str.to_re",
        # RegLan Theory
        "re.none", "re.all", "re.allchar", "re.union", "re.inter", "re.++",
        "re.comp", "re.diff", "re.*", "re.+", "re.opt", "re.loop", "re.range",
        # cvc5-specific extensions
        "str.update", "str.rev", "str.to_lower", "str.to_upper", "str.indexof_re",
    }
    
    # Character set for generating string literals, excluding the double quote.
    _PRINTABLE_ASCII_NO_DBL_QUOTE = ''.join(c for c in string.printable if c not in '"\n\r\t\x0b\x0c\\')

    def __init__(self):
        self.max_depth = random.randint(4, 7)
        self.decls = []
        self.used_names = set(self._KEYWORDS)
        self.variables = {'Bool': [], 'String': [], 'Int': [], 'RegLan': []}
        
        # Pre-populate with some initial variables for each sort to ensure
        # base cases are always available.
        for sort in self.variables.keys():
            for _ in range(random.randint(2, 4)):
                self._create_new_variable(sort)

    def generate(self):
        """Generates the top-level Boolean term."""
        return self._gen_bool_term(0)

    # --- Name and Variable Management ---

    def _generate_name(self):
        """Generates a new random name that is not a keyword."""
        while True:
            name_len = random.randint(5, 12)
            name = ''.join(random.choices(string.ascii_lowercase, k=name_len))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _create_new_variable(self, sort):
        """Creates a new variable of a given sort and adds its declaration."""
        name = self._generate_name()
        self.variables[sort].append(name)
        self.decls.append(f"(declare-const {name} {sort})")
        return name

    def _get_variable(self, sort):
        """
        Gets a variable for a given sort. It may either reuse an existing
        variable or create a new one to increase diversity.
        """
        if not self.variables[sort] or random.random() < 0.2:
            return self._create_new_variable(sort)
        return random.choice(self.variables[sort])

    # --- Lexical Terminal Generators ---

    def _gen_numeral(self):
        return str(random.randint(0, 1000))

    def _gen_string_literal(self, max_len=20):
        length = random.randint(0, max_len)
        chars = random.choices(self._PRINTABLE_ASCII_NO_DBL_QUOTE, k=length)
        return '"' + ''.join(chars) + '"'

    def _gen_char_literal(self):
        """Generates a string literal containing a single character."""
        char = random.choice(self._PRINTABLE_ASCII_NO_DBL_QUOTE)
        return f'"{char}"'

    # --- Term Generators (one per non-terminal in the CFG) ---

    def _gen_bool_term(self, depth):
        if depth >= self.max_depth:
            # Base cases for recursion termination
            return random.choice(['true', 'false', self._get_variable('Bool')])

        productions = [
            lambda: 'true',
            lambda: 'false',
            lambda: self._get_variable('Bool'),
            lambda: f"(not {self._gen_bool_term(depth + 1)})",
            lambda: self._gen_n_ary_bool_op(depth),
            lambda: f"(ite {self._gen_bool_term(depth + 1)} {self._gen_bool_term(depth + 1)} {self._gen_bool_term(depth + 1)})",
            lambda: f"(= {self._gen_int_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(= {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(= {self._gen_bool_term(depth + 1)} {self._gen_bool_term(depth + 1)})",
            lambda: self._gen_distinct_op(depth),
            lambda: f"({random.choice(['str.<', 'str.<='])} {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"({random.choice(['str.prefixof', 'str.suffixof', 'str.contains'])} {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.is_digit {self._gen_string_term(depth + 1)})",
            lambda: f"({random.choice(['<', '<=', '>', '>='])} {self._gen_int_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(str.in_re {self._gen_string_term(depth + 1)} {self._gen_reglan_term(depth + 1)})"
        ]
        return random.choice(productions)()

    def _gen_string_term(self, depth):
        if depth >= self.max_depth:
            return random.choice([self._gen_string_literal(), self._get_variable('String')])

        productions = [
            self._gen_string_literal,
            lambda: self._get_variable('String'),
            lambda: self._gen_n_ary_op('str.++', self._gen_string_term, depth, min_args=1),
            lambda: f"(str.at {self._gen_string_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(str.substr {self._gen_string_term(depth + 1)} {self._gen_int_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(str.replace {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.replace_all {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.replace_re {self._gen_string_term(depth + 1)} {self._gen_reglan_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.replace_re_all {self._gen_string_term(depth + 1)} {self._gen_reglan_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.from_int {self._gen_int_term(depth + 1)})",
            lambda: f"(str.from_code {self._gen_int_term(depth + 1)})",
            lambda: f"(ite {self._gen_bool_term(depth + 1)} {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.update {self._gen_string_term(depth + 1)} {self._gen_int_term(depth + 1)} {self._gen_string_term(depth + 1)})",
            lambda: f"(str.rev {self._gen_string_term(depth + 1)})",
            lambda: f"(str.to_lower {self._gen_string_term(depth + 1)})",
            lambda: f"(str.to_upper {self._gen_string_term(depth + 1)})",
        ]
        return random.choice(productions)()

    def _gen_int_term(self, depth):
        if depth >= self.max_depth:
            return random.choice([self._gen_numeral(), self._get_variable('Int')])
        
        productions = [
            self._gen_numeral,
            lambda: self._get_variable('Int'),
            lambda: self._gen_n_ary_op(random.choice(['+', '*']), self._gen_int_term, depth),
            lambda: self._gen_sub_op(depth),
            lambda: self._gen_n_ary_op('div', self._gen_int_term, depth),
            lambda: f"(mod {self._gen_int_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(abs {self._gen_int_term(depth + 1)})",
            lambda: f"(ite {self._gen_bool_term(depth + 1)} {self._gen_int_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(str.len {self._gen_string_term(depth + 1)})",
            lambda: f"(str.to_int {self._gen_string_term(depth + 1)})",
            lambda: f"(str.to_code {self._gen_string_term(depth + 1)})",
            lambda: f"(str.indexof {self._gen_string_term(depth + 1)} {self._gen_string_term(depth + 1)} {self._gen_int_term(depth + 1)})",
            lambda: f"(str.indexof_re {self._gen_string_term(depth + 1)} {self._gen_reglan_term(depth + 1)} {self._gen_int_term(depth + 1)})",
        ]
        return random.choice(productions)()

    def _gen_reglan_term(self, depth):
        if depth >= self.max_depth:
            return random.choice(['re.none', 're.all', 're.allchar', self._get_variable('RegLan')])
        
        productions = [
            lambda: self._get_variable('RegLan'),
            lambda: 're.none',
            lambda: 're.all',
            lambda: 're.allchar',
            lambda: f"(str.to_re {self._gen_string_term(depth + 1)})",
            lambda: self._gen_n_ary_op(random.choice(['re.union', 're.inter', 're.++']), self._gen_reglan_term, depth, min_args=1),
            lambda: f"(re.comp {self._gen_reglan_term(depth + 1)})",
            lambda: f"(re.diff {self._gen_reglan_term(depth + 1)} {self._gen_reglan_term(depth + 1)})",
            lambda: f"({random.choice(['re.*', 're.+', 're.opt'])} {self._gen_reglan_term(depth + 1)})",
            lambda: self._gen_re_loop(depth),
            lambda: f"(re.range {self._gen_char_literal()} {self._gen_char_literal()})",
            lambda: f"(ite {self._gen_bool_term(depth + 1)} {self._gen_reglan_term(depth + 1)} {self._gen_reglan_term(depth + 1)})",
        ]
        return random.choice(productions)()

    # --- Helper methods for complex or n-ary productions ---

    def _gen_n_ary_op(self, op, term_generator, depth, min_args=2, max_args=5):
        num_args = random.randint(min_args, max_args)
        if min_args == 1 and num_args == 1 and random.random() < 0.8:
            num_args = random.randint(2, max_args)
        args = [term_generator(depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"

    def _gen_n_ary_bool_op(self, depth):
        op = random.choice(['and', 'or', 'xor', '=>'])
        num_args = random.randint(2, 5)
        args = [self._gen_bool_term(depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
        
    def _gen_distinct_op(self, depth):
        num_args = random.randint(2, 5)
        if random.random() < 0.5:
            args = [self._gen_int_term(depth + 1) for _ in range(num_args)]
        else:
            args = [self._gen_string_term(depth + 1) for _ in range(num_args)]
        return f"(distinct {' '.join(args)})"

    def _gen_sub_op(self, depth):
        num_args = random.randint(1, 4)
        args = [self._gen_int_term(depth + 1) for _ in range(num_args)]
        return f"(- {' '.join(args)})"

    def _gen_re_loop(self, depth):
        n1 = random.randint(0, 10)
        n2 = random.randint(n1, n1 + 10)
        return f"(re.loop {self._gen_reglan_term(depth + 1)} {n1} {n2})"


def generate_cvc5strings_formula_with_decls():
    """
    Generates a random SMT-LIB formula for the cvc5_Strings theory.

    This function implements a random generator that strictly follows the provided
    CFG, ensuring the production of diverse and well-structured SMT-LIB terms.

    Returns:
        A tuple (decls, formula):
        - decls (str): A string containing all necessary SMT-LIB `(declare-const ...)`
          statements for the variables used in the formula, separated by newlines.
        - formula (str): A single SMT-LIB term of sort Bool representing the
          generated formula.
    """
    generator = _CVC5StringsFormulaGenerator()
    formula_str = generator.generate()
    # The declarations are collected in sorted order for consistent output
    decls_str = "\n".join(sorted(generator.decls))
    return decls_str, formula_str