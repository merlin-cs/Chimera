import random
import string

# --- Configurable parameters ---
DEFAULT_VARIABLES = 3
DEFAULT_DEPTH = 3

CMP_OPS = ["=", "<", "<=", ">", ">="]
FUNC_NAMES = [
    "sqrt", "exp",
    "sin", "cos", "tan",
    "csc", "sec", "cot",
    "arcsin", "arccos", "arctan",
    "arccsc", "arcsec", "arccot"
]

def random_variable(existing_vars):
    return random.choice(existing_vars)

def random_numeral():
    return str(random.randint(0, 100))

def random_decimal():
    return f"{random.randint(0, 100)}.{random.randint(0, 999999)}"

def random_atomic(existing_vars, depth):
    choices = ['numeral', 'decimal', 'variable', 'pi', 'function', 'paren']
    if depth <= 0:
        choices = ['numeral', 'decimal', 'variable', 'pi']
    kind = random.choice(choices)
    if kind == 'numeral':
        return random_numeral()
    elif kind == 'decimal':
        return random_decimal()
    elif kind == 'variable':
        return random_variable(existing_vars)
    elif kind == 'pi':
        return 'real.pi'
    elif kind == 'function':
        return random_function_app(existing_vars, depth-1)
    elif kind == 'paren':
        return f"({random_arith_expr(existing_vars, depth-1)})"

def random_function_app(existing_vars, depth):
    fname = random.choice(FUNC_NAMES)
    arg = random_arith_expr(existing_vars, depth-1)
    return f"({fname} {arg})"

def random_arith_factor(existing_vars, depth):
    if random.random() < 0.2 and depth > 0:
        return f"(- {random_arith_factor(existing_vars, depth-1)})"
    else:
        return random_atomic(existing_vars, depth)

def random_arith_term(existing_vars, depth):
    if depth > 0 and random.random() < 0.5:
        left = random_arith_term(existing_vars, depth-1)
        right = random_arith_factor(existing_vars, depth-1)
        return f"(* {left} {right})"
    else:
        return random_arith_factor(existing_vars, depth)

def random_arith_expr(existing_vars, depth):
    if depth > 0 and random.random() < 0.5:
        left = random_arith_expr(existing_vars, depth-1)
        op = random.choice(['+', '-'])
        right = random_arith_term(existing_vars, depth-1)
        return f"({op} {left} {right})"
    else:
        return random_arith_term(existing_vars, depth)

def random_comparison(existing_vars, depth):
    op = random.choice(CMP_OPS)
    left = random_arith_expr(existing_vars, depth-1)
    right = random_arith_expr(existing_vars, depth-1)
    return f"({op} {left} {right})"

def random_bool_term(existing_vars, depth):
    if depth <= 0:
        return random_comparison(existing_vars, 1)
    kind = random.choices(
        ['and', 'or', 'not', 'cmp'],
        weights=[0.3, 0.3, 0.2, 0.2]
    )[0]
    if kind == 'and':
        n = random.randint(2, 3)
        terms = [random_bool_term(existing_vars, depth-1) for _ in range(n)]
        return f"(and {' '.join(terms)})"
    elif kind == 'or':
        n = random.randint(2, 3)
        terms = [random_bool_term(existing_vars, depth-1) for _ in range(n)]
        return f"(or {' '.join(terms)})"
    elif kind == 'not':
        term = random_bool_term(existing_vars, depth-1)
        return f"(not {term})"
    else:
        return random_comparison(existing_vars, depth-1)

def random_variable_name(existing_names):
    while True:
        name = random.choice(string.ascii_lowercase)
        name += ''.join(random.choices(string.ascii_lowercase + string.digits + '_', k=random.randint(3, 5)))
        if name not in existing_names:
            return name

def generate_variables(n):
    names = []
    while len(names) < n:
        name = random_variable_name(names)
        names.append(name)
    return names

def generate_trans_formula(num_vars=DEFAULT_VARIABLES, depth=DEFAULT_DEPTH, seed=None):
    if seed is not None:
        random.seed(seed)
    vars = generate_variables(num_vars)
    formula = random_bool_term(vars, depth)
    decls = [f"(declare-fun {v} () Real)" for v in vars]
    # return '\n'.join(decls) + f"\n\n(assert {formula})"
    return decls, formula

# Example usage:
if __name__ == "__main__":
    print(generate_trans_formula(num_vars=3, depth=3, seed=42))