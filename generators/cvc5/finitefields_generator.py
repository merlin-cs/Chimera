import random

# ============================================================================
# SMT-LIB Finite Fields (QF_FF) Random Formula Generator
# ============================================================================

# Reserved SMT-LIB keywords to avoid
RESERVED_KEYWORDS = {
    'true', 'false', 'not', 'and', 'or', 'xor', 'ite', 'let', 'exists', 
    'forall', 'as', 'assert', 'check', 'sat', 'declare', 'fun', 'const',
    'sort', 'define', 'push', 'pop', 'get', 'set', 'logic', 'info', 'option',
    'ff', 'add', 'mul', 'neg', 'bitsum', 'FiniteField'
}

# Small primes for finite field sorts
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

# ============================================================================
# Name Generation
# ============================================================================

def generate_name(min_length=5):
    """Generate a random lowercase name of at least min_length characters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in RESERVED_KEYWORDS:
            return name

# ============================================================================
# Context and State Management
# ============================================================================

class GeneratorContext:
    def __init__(self, max_depth=6):
        self.max_depth = max_depth
        self.current_depth = 0
        
        # Choose a single prime for this generation session
        self.prime = random.choice(PRIMES)
        self.ff_sort = f"(_ FiniteField {self.prime})"
        
        # Variables
        self.bool_vars = []
        self.ff_vars = []
        
        # Generate initial variables
        num_bool_vars = random.randint(1, 4)
        num_ff_vars = random.randint(2, 5)
        
        for _ in range(num_bool_vars):
            self.bool_vars.append(generate_name())
        
        for _ in range(num_ff_vars):
            self.ff_vars.append(generate_name())
    
    def get_declarations(self):
        """Generate SMT-LIB declarations for all variables."""
        decls = []
        for bv in self.bool_vars:
            decls.append(f"(declare-const {bv} Bool)")
        for fv in self.ff_vars:
            decls.append(f"(declare-const {fv} {self.ff_sort})")
        return '\n'.join(decls)

# ============================================================================
# Finite Field Term Generation
# ============================================================================

def generate_ff_value(ctx):
    """Generate a finite field value literal."""
    # Generate a value in range [-prime+1, prime-1]
    value = random.randint(-(ctx.prime - 1), ctx.prime - 1)
    return f"(as ff{value} {ctx.ff_sort})"

def generate_ff_var(ctx):
    """Select a random finite field variable."""
    return random.choice(ctx.ff_vars)

def generate_ff_addition(ctx):
    """Generate ff.add with 2+ operands."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 4)
    operands = [generate_ff_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(ff.add {' '.join(operands)})"

def generate_ff_multiplication(ctx):
    """Generate ff.mul with 2+ operands."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 4)
    operands = [generate_ff_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(ff.mul {' '.join(operands)})"

def generate_ff_negation(ctx):
    """Generate ff.neg (experimental)."""
    ctx.current_depth += 1
    operand = generate_ff_term(ctx)
    ctx.current_depth -= 1
    return f"(ff.neg {operand})"

def generate_ff_bitsum(ctx):
    """Generate ff.bitsum with 2+ operands (experimental)."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 4)  # Changed from (1, 4) to (2, 4)
    operands = [generate_ff_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(ff.bitsum {' '.join(operands)})"

def generate_ff_ite(ctx):
    """Generate (ite bool-cond ff-term1 ff-term2)."""
    ctx.current_depth += 1
    cond = generate_bool_term(ctx)
    then_term = generate_ff_term(ctx)
    else_term = generate_ff_term(ctx)
    ctx.current_depth -= 1
    return f"(ite {cond} {then_term} {else_term})"

def generate_ff_term(ctx):
    """Generate a finite field term."""
    if ctx.current_depth >= ctx.max_depth:
        # At max depth, only generate leaves
        choice = random.choice(['value', 'var'])
        if choice == 'value':
            return generate_ff_value(ctx)
        else:
            return generate_ff_var(ctx)
    
    # Weighted choices for diversity
    choices = [
        ('value', 15),
        ('var', 15),
        ('add', 12),
        ('mul', 12),
        ('neg', 8),
        ('bitsum', 6),
        ('ite', 8)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'value':
        return generate_ff_value(ctx)
    elif choice == 'var':
        return generate_ff_var(ctx)
    elif choice == 'add':
        return generate_ff_addition(ctx)
    elif choice == 'mul':
        return generate_ff_multiplication(ctx)
    elif choice == 'neg':
        return generate_ff_negation(ctx)
    elif choice == 'bitsum':
        return generate_ff_bitsum(ctx)
    else:  # ite
        return generate_ff_ite(ctx)

# ============================================================================
# Boolean Term Generation
# ============================================================================

def generate_bool_const(ctx):
    """Generate true or false."""
    return random.choice(['true', 'false'])

def generate_bool_var(ctx):
    """Select a random boolean variable."""
    return random.choice(ctx.bool_vars)

def generate_equality_term(ctx):
    """Generate (= ff-term1 ff-term2 ...)."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 3)
    operands = [generate_ff_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(= {' '.join(operands)})"

def generate_bool_not(ctx):
    """Generate (not bool-term)."""
    ctx.current_depth += 1
    operand = generate_bool_term(ctx)
    ctx.current_depth -= 1
    return f"(not {operand})"

def generate_bool_and(ctx):
    """Generate (and bool-term1 bool-term2 ...)."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 4)
    operands = [generate_bool_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(and {' '.join(operands)})"

def generate_bool_or(ctx):
    """Generate (or bool-term1 bool-term2 ...)."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 4)
    operands = [generate_bool_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(or {' '.join(operands)})"

def generate_bool_xor(ctx):
    """Generate (xor bool-term1 bool-term2 ...)."""
    ctx.current_depth += 1
    num_operands = random.randint(2, 3)
    operands = [generate_bool_term(ctx) for _ in range(num_operands)]
    ctx.current_depth -= 1
    return f"(xor {' '.join(operands)})"

def generate_bool_implies(ctx):
    """Generate (=> bool-term1 bool-term2)."""
    ctx.current_depth += 1
    left = generate_bool_term(ctx)
    right = generate_bool_term(ctx)
    ctx.current_depth -= 1
    return f"(=> {left} {right})"

def generate_bool_ite(ctx):
    """Generate (ite bool-cond bool-then bool-else)."""
    ctx.current_depth += 1
    cond = generate_bool_term(ctx)
    then_term = generate_bool_term(ctx)
    else_term = generate_bool_term(ctx)
    ctx.current_depth -= 1
    return f"(ite {cond} {then_term} {else_term})"

def generate_bool_term(ctx):
    """Generate a boolean term."""
    if ctx.current_depth >= ctx.max_depth:
        # At max depth, only generate leaves
        choice = random.choice(['const', 'var', 'eq'])
        if choice == 'const':
            return generate_bool_const(ctx)
        elif choice == 'var':
            return generate_bool_var(ctx)
        else:
            return generate_equality_term(ctx)
    
    # Weighted choices for diversity
    choices = [
        ('const', 8),
        ('var', 10),
        ('eq', 15),
        ('not', 10),
        ('and', 12),
        ('or', 12),
        ('xor', 8),
        ('implies', 8),
        ('ite', 7)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'const':
        return generate_bool_const(ctx)
    elif choice == 'var':
        return generate_bool_var(ctx)
    elif choice == 'eq':
        return generate_equality_term(ctx)
    elif choice == 'not':
        return generate_bool_not(ctx)
    elif choice == 'and':
        return generate_bool_and(ctx)
    elif choice == 'or':
        return generate_bool_or(ctx)
    elif choice == 'xor':
        return generate_bool_xor(ctx)
    elif choice == 'implies':
        return generate_bool_implies(ctx)
    else:  # ite
        return generate_bool_ite(ctx)

# ============================================================================
# Main Generation Function
# ============================================================================

def generate_finitefields_formula_with_decls():
    """
    Generate a random SMT-LIB2 formula in the Finite Fields theory.
    
    Returns:
        tuple: (decls, formula) where
            - decls: string of SMT-LIB2 declarations
            - formula: string of a single Boolean term
    """
    # Create context with random depth limit
    max_depth = random.randint(4, 7)
    ctx = GeneratorContext(max_depth=max_depth)
    
    # Generate the formula
    formula = generate_bool_term(ctx)
    
    # Get declarations
    decls = ctx.get_declarations()
    
    return decls, formula