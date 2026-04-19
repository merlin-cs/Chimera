# complete Python module
import random
import string

# A set of SMT-LIB keywords to avoid when generating symbol names.
_SMT_KEYWORDS = {
    "abs", "and", "assert", "check-sat", "const", "declare-const",
    "declare-fun", "declare-sort", "define-fun", "distinct", "div", "echo",
    "error", "exists", "exit", "false", "forall", "get-assertions",
    "get-assignment", "get-info", "get-model", "get-option", "get-proof",
    "get-unsat-assumptions", "get-unsat-core", "get-value", "implies",
    "is_int", "ite", "let", "mod", "not", "or", "par", "pop", "push", "rem",
    "reset", "set-info", "set-logic", "set-option", "to_int", "to_real",
    "true", "xor", "declare-var", "define-fun-rec", "check-sat-assuming",
    "declare-datatypes", "define-funs-rec", "define-sort", "synth-fun",
}

class _GenerationContext:
    """Holds the state for a single formula generation task."""
    def __init__(self, max_depth, num_bool_vars, num_real_vars):
        self.max_depth = max_depth
        self.bool_vars = []
        self.real_vars = []
        self.all_symbols = set()

        for _ in range(num_bool_vars):
            name = _generate_symbol_name(self.all_symbols)
            self.all_symbols.add(name)
            self.bool_vars.append(name)

        for _ in range(num_real_vars):
            name = _generate_symbol_name(self.all_symbols)
            self.all_symbols.add(name)
            self.real_vars.append(name)

def _generate_symbol_name(existing_names):
    """Generates a random, valid, and unique SMT-LIB symbol name."""
    while True:
        length = random.randint(5, 10)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in _SMT_KEYWORDS and name not in existing_names:
            return name

def _generate_real_term(context, depth):
    """Recursively generates a term of sort Real based on the CFG."""
    # At max depth, we must choose a terminal production.
    if depth >= context.max_depth:
        # Terminal choices: literal or variable
        choices = []
        # Numerals and decimals - must be in Real format (e.g., "1.0", "12.345")
        choices.append(lambda: f"{random.randint(0, 100)}.0")
        choices.append(lambda: f"{random.randint(0, 50)}.{random.randint(0, 999):03d}")
        # Real variables
        if context.real_vars:
            choices.append(lambda: random.choice(context.real_vars))
        
        production = random.choice(choices)
        return production()

    # Productions for non-terminal levels, weighted for diversity.
    productions = []
    weights = []

    # Terminal productions (higher weight to encourage smaller terms)
    productions.append(lambda: f"{random.randint(0, 100)}.0")
    weights.append(10)
    productions.append(lambda: f"{random.randint(0, 50)}.{random.randint(0, 999):03d}")
    weights.append(10)
    if context.real_vars:
        productions.append(lambda: random.choice(context.real_vars))
        weights.append(15)

    # Recursive productions
    # Unary negation: ("-" <real_term>)
    productions.append(lambda: f"(- {_generate_real_term(context, depth + 1)})")
    weights.append(10)

    # N-ary arithmetic: ("-" | "+" | "*" | "/") <real_term> <real_term>+
    def gen_nary_arith_op():
        op = random.choice(["-", "+", "*", "/"])
        num_args = random.randint(2, 4)
        args = [_generate_real_term(context, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    productions.append(gen_nary_arith_op)
    weights.append(25)

    # ITE: ("ite" <bool_term> <real_term> <real_term>)
    def gen_ite_real():
        cond = _generate_bool_term(context, depth + 1)
        then = _generate_real_term(context, depth + 1)
        else_ = _generate_real_term(context, depth + 1)
        return f"(ite {cond} {then} {else_})"
    productions.append(gen_ite_real)
    weights.append(15)
    
    chosen_production = random.choices(productions, weights=weights, k=1)[0]
    return chosen_production()

def _generate_bool_term(context, depth):
    """Recursively generates a term of sort Bool based on the CFG."""
    # At max depth, we must choose a terminal production.
    if depth >= context.max_depth:
        choices = [lambda: "true", lambda: "false"]
        if context.bool_vars:
            choices.append(lambda: random.choice(context.bool_vars))
        
        production = random.choice(choices)
        return production()

    productions = []
    weights = []

    # Terminal productions
    productions.extend([lambda: "true", lambda: "false"])
    weights.extend([5, 5])
    if context.bool_vars:
        productions.append(lambda: random.choice(context.bool_vars))
        weights.append(10)

    # Recursive productions
    # Not: ("not" <bool_term>)
    productions.append(lambda: f"(not {_generate_bool_term(context, depth + 1)})")
    weights.append(10)

    # N-ary connectives: ("and" | "or" | "xor" | "=>") <bool_term> <bool_term>+
    def gen_nary_bool_op():
        op = random.choice(["and", "or", "xor", "=>"])
        num_args = random.randint(2, 4)
        args = [_generate_bool_term(context, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    productions.append(gen_nary_bool_op)
    weights.append(15)

    # ITE (bool): ("ite" <bool_term> <bool_term> <bool_term>)
    def gen_ite_bool():
        cond = _generate_bool_term(context, depth + 1)
        then = _generate_bool_term(context, depth + 1)
        else_ = _generate_bool_term(context, depth + 1)
        return f"(ite {cond} {then} {else_})"
    productions.append(gen_ite_bool)
    weights.append(10)

    # Equality/Distinctness on booleans
    def gen_eq_bool():
        op = random.choice(["=", "distinct"])
        num_args = random.randint(2, 4)
        args = [_generate_bool_term(context, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    productions.append(gen_eq_bool)
    weights.append(5)

    # Productions requiring real terms (only if real variables exist)
    if context.real_vars:
        # Equality/Distinctness on reals
        def gen_eq_real():
            op = random.choice(["=", "distinct"])
            num_args = random.randint(2, 4)
            args = [_generate_real_term(context, depth + 1) for _ in range(num_args)]
            return f"({op} {' '.join(args)})"
        productions.append(gen_eq_real)
        weights.append(15)

        # Relational operators (core of Reals theory)
        def gen_rel_op():
            op = random.choice(["<=", "<", ">=", ">"])
            num_args = random.randint(2, 4)
            args = [_generate_real_term(context, depth + 1) for _ in range(num_args)]
            return f"({op} {' '.join(args)})"
        productions.append(gen_rel_op)
        weights.append(25)

    chosen_production = random.choices(productions, weights=weights, k=1)[0]
    return chosen_production()

def generate_reals_formula_with_decls():
    """
    Generates a random SMT-LIB2 formula in the Reals theory.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): SMT-LIB2 declarations for all generated symbols.
        - formula (str): A single SMT-LIB2 Boolean term.
    """
    # 1. Randomize generation parameters for diversity
    max_depth = random.randint(3, 6)
    # Ensure at least one variable of each type to enable all grammar rules
    num_bool_vars = random.randint(1, 5)
    num_real_vars = random.randint(1, 5)

    # 2. Create the context and generate symbols
    context = _GenerationContext(max_depth, num_bool_vars, num_real_vars)

    # 3. Generate the declaration strings
    decls = []
    for var in context.bool_vars:
        decls.append(f"(declare-const {var} Bool)")
    for var in context.real_vars:
        decls.append(f"(declare-const {var} Real)")
    decls_str = "\n".join(decls)

    # 4. Generate the formula starting from the <bool_term> root
    formula_str = _generate_bool_term(context, 0)

    return decls_str, formula_str