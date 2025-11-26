import random
import string

# Random SMT-LIB2 formula generator for the Reals theory
# Generates declarations and a single Boolean formula over Reals.

def generate_real_formula_with_decls(max_vars=5, max_depth=3):
    """
    Generates SMT-LIB2 declarations and a random Boolean formula over Reals.

    Returns:
        decls (str): SMT-LIB2 declarations for Real variables.
        formula (str): A well-formed Boolean term (without 'assert').
    """
    # Helpers to create random identifiers
    def random_symbol(length=1):
        first_chars = string.ascii_letters
        other_chars = first_chars + string.digits
        name = random.choice(first_chars)
        name += ''.join(random.choice(other_chars) for _ in range(length))
        return name

    # Generate a pool of variable symbols
    num_vars = random.randint(1, max_vars)
    symbols = [random_symbol(5) for _ in range(num_vars)]

    # Build declarations
    decls = []
    for sym in symbols:
        decls.append(f"(declare-fun {sym} () Real)")
    decls_str = "\n".join(decls)

    # Grammar-driven random term generation
    rel_ops = ['<', '>', '<=', '>=']
    bool_ops = ['and', 'or', 'xor']
    arith_bin = ['+', '-', '*', '/']

    def gen_numeral():
        return str(random.randint(0, 10))

    def gen_decimal():
        return f"{random.randint(0, 10)}.{random.randint(0, 99):02d}"

    def gen_real_atom(depth):
        choice = random.choice(['numeral', 'decimal', 'symbol', 'neg', 'div'])
        if choice == 'numeral':
            return gen_numeral()
        if choice == 'decimal':
            return gen_decimal()
        if choice == 'symbol':
            return random.choice(symbols)
        if choice == 'neg':
            term = gen_real_term(depth+1)
            return f"(- {term})"
        left = gen_real_term(depth+1)
        right = gen_real_term(depth+1)
        return f"(/ {left} {right})"

    def gen_real_term(depth):
        if depth > max_depth:
            return random.choice(symbols + [gen_numeral(), gen_decimal()])
        form = random.choice(['atom', 'bin', 'left_assoc'])
        if form == 'atom':
            return gen_real_atom(depth)
        if form == 'bin':
            op = random.choice(['-', '/'])
            a = gen_real_term(depth+1)
            b = gen_real_term(depth+1)
            return f"({op} {a} {b})"
        op = random.choice(arith_bin)
        arity = random.randint(2, 3)
        terms = [gen_real_term(depth+1) for _ in range(arity)]
        return f"({op} {' '.join(terms)})"

    def gen_bool_term(depth):
        if depth > max_depth:
            # Base case: must return a valid Boolean term
            a = gen_real_term(depth+1)
            b = gen_real_term(depth+1)
            return f"(< {a} {b})"

        choice = random.choice([
            'not', 'imp', 'bool_op', 'eq', 'rel', 'chain', 'distinct'
        ])
        if choice == 'not':
            t = gen_bool_term(depth+1)
            return f"(not {t})"
        if choice == 'imp':
            a = gen_bool_term(depth+1)
            b = gen_bool_term(depth+1)
            return f"(=> {a} {b})"
        if choice == 'bool_op':
            op = random.choice(bool_ops)
            arity = random.randint(2, 3)
            terms = [gen_bool_term(depth+1) for _ in range(arity)]
            return f"({op} {' '.join(terms)})"
        if choice == 'eq':
            a = gen_real_term(depth+1)
            b = gen_real_term(depth+1)
            return f"(= {a} {b})"
        if choice == 'rel':
            op = random.choice(rel_ops)
            a = gen_real_term(depth+1)
            b = gen_real_term(depth+1)
            return f"({op} {a} {b})"
        if choice == 'chain':
            op = random.choice(rel_ops)
            k = random.randint(2, 4)
            terms = [gen_real_term(depth+1) for _ in range(k)]
            return f"({op} {' '.join(terms)})"
        k = random.randint(2, 4)
        terms = [gen_real_term(depth+1) for _ in range(k)]
        return f"(distinct {' '.join(terms)})"

    # Generate the Boolean formula
    formula = gen_bool_term(0)
    return decls_str, formula

# Example invocation
if __name__ == "__main__":
    decls, fm = generate_real_formula_with_decls()
    print(decls)
    print(fm)