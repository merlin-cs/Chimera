# complete Python module
import random
import string

# A set of SMT-LIB keywords to avoid when generating random symbol names.
_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "let", "forall",
    "exists", "match", "assert", "check-sat", "check-sat-assuming",
    "declare-const", "declare-fun", "declare-sort", "define-fun", "define-sort",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-core", "get-value", "pop", "push",
    "reset", "reset-assertions", "set-info", "set-logic", "set-option",
    "_", "as", "DECIMAL", "NUMERAL", "STRING", "HEXADECIMAL", "BINARY",
    "Bool", "Int", "Real", "String", "Array", "BitVec", "FiniteField",
    "ff.add", "ff.mul", "ff.neg", "ff.bitsum"
}

# A list of small prime numbers to be used for the order of finite fields.
_SMALL_PRIMES = [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113
]

# Configuration for the generator
_MIN_NAME_LENGTH = 5
_MAX_NAME_LENGTH = 8
_MAX_ARITY = 4  # For n-ary operators like 'and', 'ff.add'
_MAX_SORTS = 2
_MAX_VARS_PER_SORT = 4


def _generate_unique_name(used_names):
    """Generates a unique random name that is not an SMT-LIB keyword."""
    while True:
        length = random.randint(_MIN_NAME_LENGTH, _MAX_NAME_LENGTH)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in used_names:
            used_names.add(name)
            return name


def _generate_ff_literal(state, target_sort):
    """Generates a finite field literal, e.g., (as ff3 <sort>)."""
    prime = state['sort_info'][target_sort]['prime']
    # Generate a value in the canonical range [0, p-1] or just outside it
    # to test solver handling of modular arithmetic.
    val = random.randint(-prime // 2, prime + prime // 2)
    return f"(as ff{val} {target_sort})"


def _generate_ff_term(state, depth, target_sort):
    """Recursively generates a term of a given finite field sort."""
    ff_vars = state['symbols'].get(target_sort, [])

    # At max depth, we must produce a terminal (variable or literal).
    if depth >= state['max_depth']:
        # If there are no variables of this sort, we must generate a literal.
        if not ff_vars:
            return _generate_ff_literal(state, target_sort)
        # Otherwise, choose between a variable and a literal.
        return random.choice(ff_vars) if random.random() < 0.7 else _generate_ff_literal(state, target_sort)

    # Define possible productions and their weights.
    # Terminals (vars/literals) become more likely as depth increases.
    terminal_weight = depth + 1
    recursive_weight = max(1, state['max_depth'] - depth)
    
    productions = []
    weights = []

    if ff_vars:
        productions.append("var")
        weights.append(terminal_weight)
    
    productions.append("literal")
    weights.append(terminal_weight)

    # Recursive productions
    ops = ["ff.add", "ff.mul", "ff.neg", "ff.bitsum"]
    productions.extend(ops)
    weights.extend([recursive_weight] * len(ops))

    choice = random.choices(productions, weights=weights, k=1)[0]

    if choice == "var":
        return random.choice(ff_vars)
    
    if choice == "literal":
        return _generate_ff_literal(state, target_sort)

    if choice == "ff.neg":
        arg = _generate_ff_term(state, depth + 1, target_sort)
        return f"(ff.neg {arg})"

    if choice in ["ff.add", "ff.mul", "ff.bitsum"]:
        # Arity must be >= 2 for these operators
        arity = random.randint(2, _MAX_ARITY)
        args = [_generate_ff_term(state, depth + 1, target_sort) for _ in range(arity)]
        return f"({choice} {' '.join(args)})"
    
    # Fallback, should not be reached
    return _generate_ff_literal(state, target_sort)


def _generate_ff_equality(state, depth):
    """Generates an equality between two finite field terms of the same sort."""
    ff_sorts = list(state['sort_info'].keys())
    if not ff_sorts:
        # This case should not happen if initialization is correct.
        # Fallback to a simple boolean expression.
        return "true"

    target_sort = random.choice(ff_sorts)
    t1 = _generate_ff_term(state, depth + 1, target_sort)
    t2 = _generate_ff_term(state, depth + 1, target_sort)
    return f"(= {t1} {t2})"


def _generate_bool_term(state, depth):
    """Recursively generates a Boolean term."""
    bool_vars = state['symbols'].get('Bool', [])

    # At max depth, produce a terminal.
    if depth >= state['max_depth']:
        choices = ["true", "false"]
        if bool_vars:
            choices.extend(bool_vars)
        return random.choice(choices)

    # Define productions and weights.
    # Favor terminals as depth increases.
    terminal_weight = depth * 2 + 1
    recursive_weight = max(1, state['max_depth'] - depth)

    productions = []
    weights = []

    # Terminal productions
    productions.extend(["true", "false"])
    weights.extend([terminal_weight, terminal_weight])
    if bool_vars:
        productions.append("var")
        weights.append(terminal_weight * len(bool_vars))

    # Recursive productions
    # Give ff_equality a higher chance to ensure the FF theory is used.
    rec_ops = {
        "ff_equality": recursive_weight * 3,
        "not": recursive_weight,
        "and": recursive_weight,
        "or": recursive_weight,
        "xor": recursive_weight,
        "=>": recursive_weight,
        "ite": recursive_weight
    }
    
    # Only allow ff_equality if FF sorts have been defined.
    if state['sort_info']:
        productions.append("ff_equality")
        weights.append(rec_ops["ff_equality"])

    productions.extend(["not", "and", "or", "xor", "=>", "ite"])
    weights.extend([rec_ops[op] for op in ["not", "and", "or", "xor", "=>", "ite"]])
    
    choice = random.choices(productions, weights=weights, k=1)[0]

    if choice == "var":
        return random.choice(bool_vars)
    if choice in ["true", "false"]:
        return choice
    if choice == "ff_equality":
        return _generate_ff_equality(state, depth)
    
    if choice == "not":
        arg = _generate_bool_term(state, depth + 1)
        return f"(not {arg})"

    if choice == "ite":
        cond = _generate_bool_term(state, depth + 1)
        then_b = _generate_bool_term(state, depth + 1)
        else_b = _generate_bool_term(state, depth + 1)
        return f"(ite {cond} {then_b} {else_b})"

    if choice in ["and", "or", "xor", "=>"]:
        # Arity must be >= 2
        arity = random.randint(2, _MAX_ARITY)
        args = [_generate_bool_term(state, depth + 1) for _ in range(arity)]
        return f"({choice} {' '.join(args)})"

    # Fallback case
    return "true"


def generate_finitefields_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB formula for the Finite_Fields theory.

    This function implements a generator based on a context-free grammar,
    ensuring that all generated symbols are declared and all expressions are
    type-correct.

    Returns:
        A tuple (decls, formula):
        - decls (str): A string of SMT-LIB declarations for all sorts and
          functions used in the formula.
        - formula (str): A single SMT-LIB Boolean term representing the
          randomly generated formula.
    """
    state = {
        'decls': [],
        'symbols': {'Bool': []},
        'sort_info': {},
        'used_names': set(_SMT_KEYWORDS),
        'max_depth': random.randint(3, 6)
    }

    # 1. Declare 1 to _MAX_SORTS finite field sorts.
    num_ff_sorts = random.randint(1, _MAX_SORTS)
    for _ in range(num_ff_sorts):
        sort_name = _generate_unique_name(state['used_names'])
        prime = random.choice(_SMALL_PRIMES)
        state['sort_info'][sort_name] = {'prime': prime}
        state['symbols'][sort_name] = []
        # Use define-sort for cleaner output
        state['decls'].append(f"(define-sort {sort_name} () (_ FiniteField {prime}))")

    # 2. Declare Boolean variables.
    num_bool_vars = random.randint(1, _MAX_VARS_PER_SORT)
    for _ in range(num_bool_vars):
        var_name = _generate_unique_name(state['used_names'])
        state['symbols']['Bool'].append(var_name)
        state['decls'].append(f"(declare-fun {var_name} () Bool)")

    # 3. Declare variables for each finite field sort.
    for sort_name in state['sort_info']:
        num_ff_vars = random.randint(2, _MAX_VARS_PER_SORT)
        for _ in range(num_ff_vars):
            var_name = _generate_unique_name(state['used_names'])
            state['symbols'][sort_name].append(var_name)
            state['decls'].append(f"(declare-fun {var_name} () {sort_name})")

    # 4. Generate the formula starting from the <bool_term> production.
    formula_str = _generate_bool_term(state, depth=0)
    decls_str = "\n".join(state['decls'])

    return decls_str, formula_str