# complete Python module
import random
import string

# --- Configuration Constants ---

_MAX_DEPTH = 5
_MAX_VARS_PER_SORT = 3
_MAX_N_ARY_ARGS = 4
_MIN_SYMBOL_LEN = 5
_MAX_SYMBOL_LEN = 8
_MAX_STRING_LITERAL_LEN = 15
_MAX_NUMERAL = 1000

_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "distinct", "=",
    "assert", "check-sat", "declare-const", "declare-fun", "define-fun", "exit",
    "get-value", "get-model", "set-logic", "set-option", "set-info", "forall", "exists",
    "let", "par", "Bool", "Int", "String", "RegLan",
    "str.in_re", "str.prefixof", "str.suffixof", "str.contains", "str.is_digit",
    "str.<", "str.<=", "str.++", "str.at", "str.substr", "str.replace", "str.replace_all",
    "str.replace_re", "str.replace_re_all", "str.from_code", "str.from_int",
    "str.to_re", "str.len", "str.indexof", "str.to_code", "str.to_int",
    "re.none", "re.all", "re.allchar", "re.++", "re.union", "re.inter",
    "re.diff", "re.*", "re.+", "re.comp", "re.opt", "re.range", "re.^", "re.loop",
    "+", "-", "*", "div", "mod", "char"
}
_ALPHABET = string.ascii_lowercase
_PRINTABLE_ASCII = ''.join(chr(c) for c in range(32, 127) if chr(c) not in '"\\')

# --- Helper Functions for Random Generation ---

def _generate_random_name(used_names):
    """Generates a unique random name that is not a keyword."""
    while True:
        length = random.randint(_MIN_SYMBOL_LEN, _MAX_SYMBOL_LEN)
        name = ''.join(random.choices(_ALPHABET, k=length))
        if name not in _SMT_KEYWORDS and name not in used_names:
            used_names.add(name)
            return name

def _generate_string_literal():
    """Generates a random SMT-LIB string literal."""
    length = random.randint(0, _MAX_STRING_LITERAL_LEN)
    chars = [random.choice(_PRINTABLE_ASCII) for _ in range(length)]
    # SMT-LIB escapes double quotes with two double quotes
    return '"' + ''.join(chars).replace('"', '""') + '"'

def _generate_numeral(non_negative=True):
    """Generates a random SMT-LIB numeral as a string."""
    if non_negative:
        return str(random.randint(0, _MAX_NUMERAL))
    return str(random.randint(-_MAX_NUMERAL, _MAX_NUMERAL))

def _generate_hexadecimal():
    """Generates a random SMT-LIB hexadecimal value for a character."""
    val = random.randint(0, 0xFF)
    return f"#x{val:02x}"

# --- Generator Context ---

class _GeneratorContext:
    """Manages state during formula generation, such as declared variables."""
    def __init__(self):
        self.used_names = set()
        self.declarations = []
        self.vars = {'Bool': [], 'String': [], 'Int': [], 'RegLan': []}
        self._initialize_variables()

    def _initialize_variables(self):
        """Creates initial variables for each sort."""
        for sort in self.vars.keys():
            num_vars = random.randint(1, _MAX_VARS_PER_SORT)
            for _ in range(num_vars):
                name = _generate_random_name(self.used_names)
                self.vars[sort].append(name)
                self.declarations.append(f"(declare-const {name} {sort})")

    def get_var(self, sort):
        """Returns a randomly chosen variable name for a given sort."""
        if not self.vars[sort]:
            # This should not happen if initialized correctly, but as a fallback:
            name = _generate_random_name(self.used_names)
            self.vars[sort].append(name)
            self.declarations.append(f"(declare-const {name} {sort})")
            return name
        return random.choice(self.vars[sort])

# --- Forward declarations for generator functions ---
_generate_bool_term = None
_generate_string_term = None
_generate_reglan_term = None
_generate_int_term = None
_generate_term = None


# --- Core Term Generation Logic ---

def _choose_production(context, depth, recursive_productions, terminal_productions):
    """
    Selects a production rule based on depth.
    At max depth, only terminal productions are chosen.
    Otherwise, a weighted choice is made between recursive and terminal rules.
    """
    prob_terminal = (depth / _MAX_DEPTH) ** 1.5 if _MAX_DEPTH > 0 else 1.0
    
    use_terminal = (depth >= _MAX_DEPTH) or \
                   (not recursive_productions) or \
                   (random.random() < prob_terminal)

    if use_terminal:
        production = random.choice(terminal_productions)
    else:
        prods, weights = zip(*recursive_productions)
        production = random.choices(prods, weights=weights, k=1)[0]
    
    return production(context, depth)

def _generate_n_ary_op(op_name, arg_generator_func, context, depth):
    """Helper to generate n-ary operators like 'and', 'or', 'str.++'."""
    num_args = random.randint(2, _MAX_N_ARY_ARGS)
    args = [arg_generator_func(context, depth + 1) for _ in range(num_args)]
    return f"({op_name} {' '.join(args)})"

def _generate_bool_term_impl(context, depth):
    """Implementation of <bool_term> generator."""
    recursive_prods = [
        (lambda c, d: f"(str.in_re {_generate_string_term(c, d + 1)} {_generate_reglan_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.prefixof {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.suffixof {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.contains {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.is_digit {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.< {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.<= {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: _generate_n_ary_op("and", _generate_bool_term, c, d), 20),
        (lambda c, d: _generate_n_ary_op("or", _generate_bool_term, c, d), 20),
        (lambda c, d: _generate_n_ary_op("xor", _generate_bool_term, c, d), 10),
        (lambda c, d: _generate_n_ary_op("=>", _generate_bool_term, c, d), 10),
        (lambda c, d: f"(not {_generate_bool_term(c, d + 1)})", 15),
        (lambda c, d: f"(ite {_generate_bool_term(c, d + 1)} {_generate_bool_term(c, d + 1)} {_generate_bool_term(c, d + 1)})", 15),
        (lambda c, d: f"(= {_generate_term(c, d + 1, same_sort=True)})", 15),
        (lambda c, d: f"(distinct {_generate_term(c, d + 1, same_sort=True, n_ary=True)})", 10),
    ]
    terminal_prods = [
        lambda c, d: "true",
        lambda c, d: "false",
        lambda c, d: c.get_var('Bool'),
    ]
    return _choose_production(context, depth, recursive_prods, terminal_prods)

def _generate_string_term_impl(context, depth):
    """Implementation of <string_term> generator."""
    recursive_prods = [
        (lambda c, d: _generate_n_ary_op("str.++", _generate_string_term, c, d), 20),
        (lambda c, d: f"(str.at {_generate_string_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.substr {_generate_string_term(c, d + 1)} {_generate_int_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.replace {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.replace_all {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.replace_re {_generate_string_term(c, d + 1)} {_generate_reglan_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.replace_re_all {_generate_string_term(c, d + 1)} {_generate_reglan_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.from_code {_generate_int_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.from_int {_generate_int_term(c, d + 1)})", 5),
        (lambda c, d: f"(ite {_generate_bool_term(c, d + 1)} {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 15),
    ]
    terminal_prods = [
        lambda c, d: _generate_string_literal(),
        lambda c, d: c.get_var('String'),
        lambda c, d: f"(_ char {_generate_hexadecimal()})",
    ]
    return _choose_production(context, depth, recursive_prods, terminal_prods)

def _generate_reglan_term_impl(context, depth):
    """Implementation of <reglan_term> generator."""
    recursive_prods = [
        (lambda c, d: f"(str.to_re {_generate_string_term(c, d + 1)})", 15),
        (lambda c, d: _generate_n_ary_op("re.++", _generate_reglan_term, c, d), 10),
        (lambda c, d: _generate_n_ary_op("re.union", _generate_reglan_term, c, d), 10),
        (lambda c, d: _generate_n_ary_op("re.inter", _generate_reglan_term, c, d), 10),
        (lambda c, d: f"(re.diff {_generate_reglan_term(c, d + 1)} {_generate_reglan_term(c, d + 1)})", 5),
        (lambda c, d: f"(re.* {_generate_reglan_term(c, d + 1)})", 10),
        (lambda c, d: f"(re.+ {_generate_reglan_term(c, d + 1)})", 10),
        (lambda c, d: f"(re.comp {_generate_reglan_term(c, d + 1)})", 5),
        (lambda c, d: f"(re.opt {_generate_reglan_term(c, d + 1)})", 5),
        (lambda c, d: f"(re.range {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)})", 10),
        (lambda c, d: f"((_ re.^ {_generate_numeral()}) {_generate_reglan_term(c, d + 1)})", 5),
        (lambda c, d: f"((_ re.loop {_generate_numeral()} {_generate_numeral()}) {_generate_reglan_term(c, d + 1)})", 5),
        (lambda c, d: f"(ite {_generate_bool_term(c, d + 1)} {_generate_reglan_term(c, d + 1)} {_generate_reglan_term(c, d + 1)})", 10),
    ]
    terminal_prods = [
        lambda c, d: "re.none",
        lambda c, d: "re.all",
        lambda c, d: "re.allchar",
        lambda c, d: c.get_var('RegLan'),
    ]
    return _choose_production(context, depth, recursive_prods, terminal_prods)

def _generate_int_term_impl(context, depth):
    """Implementation of <int_term> generator."""
    recursive_prods = [
        (lambda c, d: f"(str.len {_generate_string_term(c, d + 1)})", 15),
        (lambda c, d: f"(str.indexof {_generate_string_term(c, d + 1)} {_generate_string_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 10),
        (lambda c, d: f"(str.to_code {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: f"(str.to_int {_generate_string_term(c, d + 1)})", 5),
        (lambda c, d: _generate_n_ary_op("+", _generate_int_term, c, d), 15),
        (lambda c, d: _generate_n_ary_op("-", _generate_int_term, c, d), 15),
        (lambda c, d: _generate_n_ary_op("*", _generate_int_term, c, d), 10),
        (lambda c, d: f"(div {_generate_int_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 5),
        (lambda c, d: f"(mod {_generate_int_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 5),
        (lambda c, d: f"(ite {_generate_bool_term(c, d + 1)} {_generate_int_term(c, d + 1)} {_generate_int_term(c, d + 1)})", 10),
    ]
    terminal_prods = [
        lambda c, d: _generate_numeral(),
        lambda c, d: f"(- {_generate_numeral()})",
        lambda c, d: c.get_var('Int'),
    ]
    return _choose_production(context, depth, recursive_prods, terminal_prods)

def _generate_term_impl(context, depth, same_sort=False, n_ary=False):
    """
    Implementation of <term> generator. Used for polymorphic operators like '='.
    If same_sort is True, generates multiple terms of the same randomly chosen sort.
    """
    sort = random.choice(['Bool', 'String', 'Int', 'RegLan'])
    gen_func = {
        'Bool': _generate_bool_term,
        'String': _generate_string_term,
        'Int': _generate_int_term,
        'RegLan': _generate_reglan_term
    }[sort]

    if not same_sort:
        return gen_func(context, depth)
    
    count = random.randint(2, _MAX_N_ARY_ARGS) if n_ary else 2
    args = [gen_func(context, depth) for _ in range(count)]
    return ' '.join(args)

# --- Function Pointers ---
# Assign implementations to the forward-declared names to allow mutual recursion.
_generate_bool_term = _generate_bool_term_impl
_generate_string_term = _generate_string_term_impl
_generate_reglan_term = _generate_reglan_term_impl
_generate_int_term = _generate_int_term_impl
_generate_term = _generate_term_impl

# --- Public API Function ---

def generate_strings_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB formula for the Strings theory.

    This function implements a recursive-descent generator based on the SMT-LIB
    Strings theory CFG. It randomizes operators, term structure, and the number
    of variables to promote diversity in the generated formulas.

    Returns:
        tuple[str, str]: A tuple containing:
            - A string of SMT-LIB declarations for all generated variables.
            - A string representing the SMT-LIB Boolean term (the formula).
    """
    context = _GeneratorContext()
    formula_str = _generate_bool_term(context, 0)
    decls_str = "\n".join(context.declarations)
    return decls_str, formula_str