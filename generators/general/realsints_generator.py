import random

# ============================================================================
# SMT-LIB2 Keywords (reserved words to avoid in symbol names)
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'assert', 'check-sat', 'declare-fun', 'declare-const', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'Int', 'Real', 'Bool', 'Array', 'BitVec',
    'div', 'mod', 'abs', 'to_int', 'to_real', 'is_int',
    'distinct', 'divisible'
}

# ============================================================================
# Random Name Generator
# ============================================================================
def generate_random_name(min_length=5):
    """Generate a random lowercase name of at least min_length characters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and depth
# ============================================================================
class GeneratorContext:
    def __init__(self, max_depth=5, max_vars_per_sort=5):
        self.max_depth = max_depth
        self.bool_vars = []
        self.int_vars = []
        self.real_vars = []
        self.max_vars_per_sort = max_vars_per_sort
        
        # Generate initial variables
        num_bool = random.randint(1, max_vars_per_sort)
        num_int = random.randint(1, max_vars_per_sort)
        num_real = random.randint(1, max_vars_per_sort)
        
        for _ in range(num_bool):
            self.bool_vars.append(generate_random_name())
        for _ in range(num_int):
            self.int_vars.append(generate_random_name())
        for _ in range(num_real):
            self.real_vars.append(generate_random_name())
    
    def get_decls(self):
        """Generate SMT-LIB2 declarations for all variables."""
        decls = []
        for var in self.bool_vars:
            decls.append(f"(declare-const {var} Bool)")
        for var in self.int_vars:
            decls.append(f"(declare-const {var} Int)")
        for var in self.real_vars:
            decls.append(f"(declare-const {var} Real)")
        return '\n'.join(decls)

# ============================================================================
# Numeral and Decimal Generators
# ============================================================================
def generate_numeral():
    """Generate a numeral (non-negative integer)."""
    return str(random.randint(0, 100))

def generate_positive_numeral():
    """Generate a positive numeral (positive integer)."""
    return str(random.randint(1, 100))

def generate_decimal():
    """Generate a decimal number."""
    int_part = random.randint(0, 100)
    frac_part = random.randint(0, 100)
    return f"{int_part}.{frac_part}"

# ============================================================================
# Term Generators
# ============================================================================
def generate_bool_term(ctx, depth=0):
    """Generate a Boolean term following the CFG."""
    if depth >= ctx.max_depth:
        # Base cases only
        choices = ['true', 'false', 'bool_var']
        choice = random.choice(choices)
    else:
        # All productions
        choices = [
            'true', 'false', 'bool_var',
            'not', 'and', 'or', 'xor', '=>',
            'bool_eq', 'bool_distinct', 'bool_ite',
            'int_comparison', 'real_comparison',
            'is_int', 'divisible'
        ]
        choice = random.choice(choices)
    
    if choice == 'true':
        return 'true'
    elif choice == 'false':
        return 'false'
    elif choice == 'bool_var':
        return random.choice(ctx.bool_vars)
    elif choice == 'not':
        inner = generate_bool_term(ctx, depth + 1)
        return f"(not {inner})"
    elif choice == 'and':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(and {' '.join(terms)})"
    elif choice == 'or':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(or {' '.join(terms)})"
    elif choice == 'xor':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(xor {' '.join(terms)})"
    elif choice == '=>':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(=> {' '.join(terms)})"
    elif choice == 'bool_eq':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(= {' '.join(terms)})"
    elif choice == 'bool_distinct':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(distinct {' '.join(terms)})"
    elif choice == 'bool_ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_bool_term(ctx, depth + 1)
        else_term = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"
    elif choice == 'int_comparison':
        return generate_int_comparison(ctx, depth + 1)
    elif choice == 'real_comparison':
        return generate_real_comparison(ctx, depth + 1)
    elif choice == 'is_int':
        real_term = generate_real_term(ctx, depth + 1)
        return f"(is_int {real_term})"
    elif choice == 'divisible':
        n = generate_positive_numeral()
        int_term = generate_int_term(ctx, depth + 1)
        return f"((_ divisible {n}) {int_term})"
    else:
        return 'true'

def generate_int_comparison(ctx, depth):
    """Generate an integer comparison."""
    ops = ['<=', '<', '>=', '>', '=', 'distinct']
    op = random.choice(ops)
    n = random.randint(2, 3)
    terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
    return f"({op} {' '.join(terms)})"

def generate_real_comparison(ctx, depth):
    """Generate a real comparison."""
    ops = ['<=', '<', '>=', '>', '=', 'distinct']
    op = random.choice(ops)
    n = random.randint(2, 3)
    terms = [generate_real_term(ctx, depth + 1) for _ in range(n)]
    return f"({op} {' '.join(terms)})"

def generate_int_term(ctx, depth=0):
    """Generate an integer term following the CFG."""
    if depth >= ctx.max_depth:
        # Base cases only
        choices = ['numeral', 'int_var']
        choice = random.choice(choices)
    else:
        # All productions
        choices = [
            'numeral', 'int_var',
            'neg', 'sub', 'add', 'mul', 'div', 'mod', 'abs',
            'to_int', 'int_ite'
        ]
        choice = random.choice(choices)
    
    if choice == 'numeral':
        return generate_numeral()
    elif choice == 'int_var':
        return random.choice(ctx.int_vars)
    elif choice == 'neg':
        inner = generate_int_term(ctx, depth + 1)
        return f"(- {inner})"
    elif choice == 'sub':
        n = random.randint(2, 3)
        terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        return f"(- {' '.join(terms)})"
    elif choice == 'add':
        n = random.randint(2, 3)
        terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        return f"(+ {' '.join(terms)})"
    elif choice == 'mul':
        n = random.randint(2, 3)
        terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        return f"(* {' '.join(terms)})"
    elif choice == 'div':
        n = random.randint(2, 3)
        terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        return f"(div {' '.join(terms)})"
    elif choice == 'mod':
        t1 = generate_int_term(ctx, depth + 1)
        t2 = generate_int_term(ctx, depth + 1)
        return f"(mod {t1} {t2})"
    elif choice == 'abs':
        inner = generate_int_term(ctx, depth + 1)
        return f"(abs {inner})"
    elif choice == 'to_int':
        real_term = generate_real_term(ctx, depth + 1)
        return f"(to_int {real_term})"
    elif choice == 'int_ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_int_term(ctx, depth + 1)
        else_term = generate_int_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"
    else:
        return '0'

def generate_real_term(ctx, depth=0):
    """Generate a real term following the CFG."""
    if depth >= ctx.max_depth:
        # Base cases only
        choices = ['decimal', 'real_var']
        choice = random.choice(choices)
    else:
        # All productions
        choices = [
            'decimal', 'real_var',
            'neg', 'sub', 'add', 'mul', 'div',
            'to_real', 'real_ite'
        ]
        choice = random.choice(choices)
    
    if choice == 'decimal':
        return generate_decimal()
    elif choice == 'real_var':
        return random.choice(ctx.real_vars)
    elif choice == 'neg':
        inner = generate_real_term(ctx, depth + 1)
        return f"(- {inner})"
    elif choice == 'sub':
        n = random.randint(2, 3)
        terms = [generate_real_term(ctx, depth + 1) for _ in range(n)]
        return f"(- {' '.join(terms)})"
    elif choice == 'add':
        n = random.randint(2, 3)
        terms = [generate_real_term(ctx, depth + 1) for _ in range(n)]
        return f"(+ {' '.join(terms)})"
    elif choice == 'mul':
        n = random.randint(2, 3)
        terms = [generate_real_term(ctx, depth + 1) for _ in range(n)]
        return f"(* {' '.join(terms)})"
    elif choice == 'div':
        n = random.randint(2, 3)
        terms = [generate_real_term(ctx, depth + 1) for _ in range(n)]
        return f"(/ {' '.join(terms)})"
    elif choice == 'to_real':
        int_term = generate_int_term(ctx, depth + 1)
        return f"(to_real {int_term})"
    elif choice == 'real_ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_real_term(ctx, depth + 1)
        else_term = generate_real_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"
    else:
        return '0.0'

# ============================================================================
# Main Generator Function
# ============================================================================
def generate_realsints_formula_with_decls():
    """Generate a random Reals_Ints formula with declarations."""
    max_depth = random.randint(3, 6)
    max_vars = random.randint(2, 5)
    
    ctx = GeneratorContext(max_depth=max_depth, max_vars_per_sort=max_vars)
    
    formula = generate_bool_term(ctx, depth=0)
    decls = ctx.get_decls()
    
    return decls, formula