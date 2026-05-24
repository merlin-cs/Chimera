import random
import string

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'true', 'false', 'and', 'or', 'not', 'xor', 'ite', 'let', 'forall', 'exists',
    'assert', 'check-sat', 'declare-fun', 'declare-const', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'Real', 'Int', 'Bool', 'Array', 'BitVec',
    'sqrt', 'exp', 'sin', 'cos', 'tan', 'csc', 'sec', 'cot',
    'arcsin', 'arccos', 'arctan', 'arccsc', 'arcsec', 'arccot',
    'abs', 'div', 'mod', 'distinct', 'real.pi'
}

# ============================================================================
# Name Generation
# ============================================================================
def generate_random_name(min_length=5):
    """Generate a random lowercase name of at least min_length characters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations
# ============================================================================
class Context:
    def __init__(self):
        self.bool_vars = []
        self.real_vars = []
        self.max_depth = random.randint(3, 6)
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
        
    def add_real_var(self, name):
        self.real_vars.append(name)
        
    def get_random_bool_var(self):
        if self.bool_vars:
            return random.choice(self.bool_vars)
        return None
        
    def get_random_real_var(self):
        if self.real_vars:
            return random.choice(self.real_vars)
        return None

# ============================================================================
# Real Term Generation
# ============================================================================
def generate_numeral():
    """Generate a numeral (non-negative integer)."""
    return str(random.randint(0, 100))

def generate_decimal():
    """Generate a decimal number."""
    int_part = random.randint(0, 100)
    frac_part = random.randint(1, 999)
    return f"{int_part}.{frac_part}"

def generate_transcendental_func(ctx, depth):
    """Generate a transcendental function application."""
    funcs = ['sqrt', 'exp', 'sin', 'cos', 'tan', 'csc', 'sec', 'cot',
             'arcsin', 'arccos', 'arctan', 'arccsc', 'arcsec', 'arccot']
    func = random.choice(funcs)
    arg = generate_real_term(ctx, depth + 1)
    return f"({func} {arg})"

def generate_arithmetic_op(ctx, depth):
    """Generate an arithmetic operation."""
    ops_binary_plus = ['+', '-', '*']
    ops_binary = ['/']
    ops_int_binary = ['div', 'mod']  # These require integer arguments
    ops_unary = ['abs']
    
    choice = random.randint(0, 10)
    if choice < 6:  # Binary+ operations (can have 2+ arguments)
        op = random.choice(ops_binary_plus)
        num_args = random.randint(2, 4)
        args = [generate_real_term(ctx, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    elif choice < 8:  # Binary operations (exactly 2 arguments)
        op = random.choice(ops_binary)
        arg1 = generate_real_term(ctx, depth + 1)
        arg2 = generate_real_term(ctx, depth + 1)
        return f"({op} {arg1} {arg2})"
    elif choice < 9:  # Integer operations (div, mod) - convert to int
        op = random.choice(ops_int_binary)
        # Generate integer terms by converting real terms to integers
        arg1 = f"(to_int {generate_real_term(ctx, depth + 1)})"
        arg2 = f"(to_int {generate_real_term(ctx, depth + 1)})"
        # Convert result back to real
        return f"(to_real ({op} {arg1} {arg2}))"
    else:  # Unary operations
        op = random.choice(ops_unary)
        arg = generate_real_term(ctx, depth + 1)
        return f"({op} {arg})"

def generate_real_term(ctx, depth):
    """Generate a real-valued term."""
    if depth >= ctx.max_depth:
        # Base case: return simple term
        choices = []
        if ctx.real_vars:
            choices.extend(['var'] * 3)
        choices.extend(['numeral', 'decimal', 'pi'])
        
        choice = random.choice(choices)
        if choice == 'var':
            return ctx.get_random_real_var()
        elif choice == 'numeral':
            return generate_numeral()
        elif choice == 'decimal':
            return generate_decimal()
        else:  # pi
            return "real.pi"
    
    # Recursive case
    choices = ['numeral', 'decimal', 'pi', 'transcendental', 'arithmetic', 'ite', 'negation']
    if ctx.real_vars:
        choices.extend(['var'] * 2)
    
    choice = random.choice(choices)
    
    if choice == 'var':
        return ctx.get_random_real_var()
    elif choice == 'numeral':
        return generate_numeral()
    elif choice == 'decimal':
        return generate_decimal()
    elif choice == 'pi':
        return "real.pi"
    elif choice == 'transcendental':
        return generate_transcendental_func(ctx, depth)
    elif choice == 'arithmetic':
        return generate_arithmetic_op(ctx, depth)
    elif choice == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_real_term(ctx, depth + 1)
        else_branch = generate_real_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    else:  # negation
        arg = generate_real_term(ctx, depth + 1)
        return f"(- {arg})"

# ============================================================================
# Boolean Term Generation
# ============================================================================
def generate_comparison(ctx, depth):
    """Generate a comparison operation."""
    ops = ['=', '<', '<=', '>', '>=', 'distinct']
    op = random.choice(ops)
    num_args = random.randint(2, 3)
    args = [generate_real_term(ctx, depth + 1) for _ in range(num_args)]
    return f"({op} {' '.join(args)})"

def generate_logical_op(ctx, depth):
    """Generate a logical operation."""
    choice = random.randint(0, 3)
    
    if choice == 0:  # and
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(and {' '.join(args)})"
    elif choice == 1:  # or
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(or {' '.join(args)})"
    elif choice == 2:  # =>
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(=> {arg1} {arg2})"
    else:  # xor
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(xor {arg1} {arg2})"

def generate_bool_term(ctx, depth):
    """Generate a Boolean term."""
    if depth >= ctx.max_depth:
        # Base case
        choices = ['true', 'false']
        if ctx.bool_vars:
            choices.extend(['var'] * 2)
        choices.append('comparison')
        
        choice = random.choice(choices)
        if choice == 'true':
            return "true"
        elif choice == 'false':
            return "false"
        elif choice == 'var':
            return ctx.get_random_bool_var()
        else:  # comparison
            return generate_comparison(ctx, depth)
    
    # Recursive case
    choices = ['true', 'false', 'comparison', 'logical', 'not']
    if ctx.bool_vars:
        choices.extend(['var'] * 2)
    
    choice = random.choice(choices)
    
    if choice == 'true':
        return "true"
    elif choice == 'false':
        return "false"
    elif choice == 'var':
        return ctx.get_random_bool_var()
    elif choice == 'comparison':
        return generate_comparison(ctx, depth)
    elif choice == 'logical':
        return generate_logical_op(ctx, depth)
    else:  # not
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"

# ============================================================================
# Main Generation Function
# ============================================================================
def generate_transcendentals_formula_with_decls():
    """Generate a random Transcendentals formula with declarations."""
    ctx = Context()
    
    # Generate random number of variables
    num_bool_vars = random.randint(1, 4)
    num_real_vars = random.randint(2, 5)
    
    # Generate variable names
    used_names = set()
    for _ in range(num_bool_vars):
        name = generate_random_name()
        while name in used_names:
            name = generate_random_name()
        used_names.add(name)
        ctx.add_bool_var(name)
    
    for _ in range(num_real_vars):
        name = generate_random_name()
        while name in used_names:
            name = generate_random_name()
        used_names.add(name)
        ctx.add_real_var(name)
    
    # Generate declarations
    decls = []
    for var in ctx.bool_vars:
        decls.append(f"(declare-const {var} Bool)")
    for var in ctx.real_vars:
        decls.append(f"(declare-const {var} Real)")
    
    decls_str = '\n'.join(decls)
    
    # Generate formula
    formula_str = generate_bool_term(ctx, 0)
    
    return decls_str, formula_str