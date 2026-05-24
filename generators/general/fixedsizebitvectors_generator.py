import random

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'let', 'exists', 
    'forall', 'assert', 'declare-fun', 'declare-const', 'define-fun',
    'check-sat', 'get-model', 'set-logic', 'set-option', 'distinct',
    'concat', 'extract', 'bvnot', 'bvneg', 'bvand', 'bvor', 'bvadd',
    'bvmul', 'bvudiv', 'bvurem', 'bvshl', 'bvlshr', 'bvult',
    'bvuaddo', 'bvsaddo', 'bvumulo', 'bvsmulo',
    'int_to_bv', 'ubv_to_int', 'sbv_to_int', 'Bool', 'Int', 'BitVec'
}

# ============================================================================
# Name Generation
# ============================================================================
def generate_name(min_length=5):
    """Generate a random name of at least min_length lowercase letters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and variables
# ============================================================================
class Context:
    def __init__(self):
        self.bool_vars = []
        self.bv_vars = {}  # {width: [var_names]}
        self.int_vars = []
        self.declarations = []
        self.depth = 0
        self.max_depth = 6
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
        self.declarations.append(f"(declare-const {name} Bool)")
        
    def add_bv_var(self, name, width):
        if width not in self.bv_vars:
            self.bv_vars[width] = []
        self.bv_vars[width].append(name)
        self.declarations.append(f"(declare-const {name} (_ BitVec {width}))")
        
    def add_int_var(self, name):
        self.int_vars.append(name)
        self.declarations.append(f"(declare-const {name} Int)")
        
    def get_decls(self):
        return '\n'.join(self.declarations)

# ============================================================================
# Bitvector Literal Generation
# ============================================================================
def generate_bv_literal(width):
    """Generate a bitvector literal of given width."""
    if random.choice([True, False]):
        # Binary literal
        bits = ''.join(random.choice('01') for _ in range(width))
        return f"#b{bits}"
    else:
        # Hex literal
        hex_digits = (width + 3) // 4
        hex_str = ''.join(random.choice('0123456789abcdef') for _ in range(hex_digits))
        return f"#x{hex_str}"

# ============================================================================
# Integer Literal Generation
# ============================================================================
def generate_int_literal():
    """Generate an integer literal."""
    val = random.randint(-100, 100)
    if val < 0:
        return f"(- {-val})"
    return str(val)

# ============================================================================
# Bitvector Term Generation
# ============================================================================
def generate_bv_term(ctx, width, allow_let=True):
    """Generate a bitvector term of given width."""
    ctx.depth += 1
    if ctx.depth > ctx.max_depth:
        ctx.depth -= 1
        return generate_bv_literal(width)
    
    choices = ['literal', 'var']
    
    if allow_let and ctx.depth < ctx.max_depth - 1:
        choices.append('let')
    
    if ctx.depth < ctx.max_depth - 1:
        choices.extend(['concat', 'extract', 'bvnot', 'bvneg', 'bvand', 'bvor', 
                       'bvadd', 'bvmul', 'bvudiv', 'bvurem', 'bvshl', 'bvlshr', 
                       'ite', 'int_to_bv'])
    
    choice = random.choice(choices)
    
    if choice == 'literal':
        result = generate_bv_literal(width)
    elif choice == 'var':
        if width in ctx.bv_vars and ctx.bv_vars[width] and random.random() < 0.7:
            result = random.choice(ctx.bv_vars[width])
        else:
            name = generate_name()
            ctx.add_bv_var(name, width)
            result = name
    elif choice == 'let':
        num_bindings = random.randint(1, 3)
        bindings = []
        for _ in range(num_bindings):
            bind_name = generate_name()
            bind_width = random.choice([width, random.choice([8, 16, 32])])
            bind_term = generate_bv_term(ctx, bind_width, allow_let=False)
            bindings.append(f"({bind_name} {bind_term})")
        body = generate_bv_term(ctx, width, allow_let=False)
        result = f"(let ({' '.join(bindings)}) {body})"
    elif choice == 'concat':
        w1 = random.randint(1, width - 1)
        w2 = width - w1
        t1 = generate_bv_term(ctx, w1, allow_let=False)
        t2 = generate_bv_term(ctx, w2, allow_let=False)
        result = f"(concat {t1} {t2})"
    elif choice == 'extract':
        source_width = width + random.randint(0, 8)
        high = random.randint(width - 1, source_width - 1)
        low = high - width + 1
        t = generate_bv_term(ctx, source_width, allow_let=False)
        result = f"((_ extract {high} {low}) {t})"
    elif choice == 'bvnot':
        t = generate_bv_term(ctx, width, allow_let=False)
        result = f"(bvnot {t})"
    elif choice == 'bvneg':
        t = generate_bv_term(ctx, width, allow_let=False)
        result = f"(bvneg {t})"
    elif choice in ['bvand', 'bvor', 'bvadd', 'bvmul']:
        # These are binary operations in standard SMT-LIB
        t1 = generate_bv_term(ctx, width, allow_let=False)
        t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"({choice} {t1} {t2})"
    elif choice in ['bvudiv', 'bvurem', 'bvshl', 'bvlshr']:
        t1 = generate_bv_term(ctx, width, allow_let=False)
        t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"({choice} {t1} {t2})"
    elif choice == 'ite':
        cond = generate_bool_term(ctx, allow_let=False)
        t1 = generate_bv_term(ctx, width, allow_let=False)
        t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"(ite {cond} {t1} {t2})"
    elif choice == 'int_to_bv':
        int_term = generate_int_term(ctx, allow_let=False)
        result = f"((_ int_to_bv {width}) {int_term})"
    else:
        result = generate_bv_literal(width)
    
    ctx.depth -= 1
    return result

# ============================================================================
# Integer Term Generation
# ============================================================================
def generate_int_term(ctx, allow_let=True):
    """Generate an integer term."""
    ctx.depth += 1
    if ctx.depth > ctx.max_depth:
        ctx.depth -= 1
        return generate_int_literal()
    
    choices = ['literal', 'var']
    
    if ctx.depth < ctx.max_depth - 1:
        choices.extend(['ubv_to_int', 'sbv_to_int', 'ite'])
    
    choice = random.choice(choices)
    
    if choice == 'literal':
        result = generate_int_literal()
    elif choice == 'var':
        if ctx.int_vars and random.random() < 0.7:
            result = random.choice(ctx.int_vars)
        else:
            name = generate_name()
            ctx.add_int_var(name)
            result = name
    elif choice == 'ubv_to_int':
        width = random.choice([8, 16, 32])
        bv = generate_bv_term(ctx, width, allow_let=False)
        result = f"(ubv_to_int {bv})"
    elif choice == 'sbv_to_int':
        width = random.choice([8, 16, 32])
        bv = generate_bv_term(ctx, width, allow_let=False)
        result = f"(sbv_to_int {bv})"
    elif choice == 'ite':
        cond = generate_bool_term(ctx, allow_let=False)
        t1 = generate_int_term(ctx, allow_let=False)
        t2 = generate_int_term(ctx, allow_let=False)
        result = f"(ite {cond} {t1} {t2})"
    else:
        result = generate_int_literal()
    
    ctx.depth -= 1
    return result

# ============================================================================
# Boolean Term Generation
# ============================================================================
def generate_bool_term(ctx, allow_let=True):
    """Generate a Boolean term."""
    ctx.depth += 1
    if ctx.depth > ctx.max_depth:
        ctx.depth -= 1
        return random.choice(['true', 'false'])
    
    choices = ['true', 'false', 'var']
    
    if allow_let and ctx.depth < ctx.max_depth - 1:
        choices.append('let')
    
    if ctx.depth < ctx.max_depth - 1:
        choices.extend(['not', 'and', 'or', 'xor', 'implies', 'equals', 
                       'distinct', 'ite', 'bvult', 'bvuaddo', 
                       'bvsaddo', 'bvumulo', 'bvsmulo'])
    
    choice = random.choice(choices)
    
    if choice == 'true':
        result = 'true'
    elif choice == 'false':
        result = 'false'
    elif choice == 'var':
        if ctx.bool_vars and random.random() < 0.7:
            result = random.choice(ctx.bool_vars)
        else:
            name = generate_name()
            ctx.add_bool_var(name)
            result = name
    elif choice == 'let':
        num_bindings = random.randint(1, 3)
        bindings = []
        for _ in range(num_bindings):
            bind_name = generate_name()
            if random.choice([True, False]):
                bind_term = generate_bool_term(ctx, allow_let=False)
            else:
                width = random.choice([8, 16, 32])
                bind_term = generate_bv_term(ctx, width, allow_let=False)
            bindings.append(f"({bind_name} {bind_term})")
        body = generate_bool_term(ctx, allow_let=False)
        result = f"(let ({' '.join(bindings)}) {body})"
    elif choice == 'not':
        t = generate_bool_term(ctx, allow_let=False)
        result = f"(not {t})"
    elif choice in ['and', 'or', 'xor']:
        # Binary operations
        t1 = generate_bool_term(ctx, allow_let=False)
        t2 = generate_bool_term(ctx, allow_let=False)
        result = f"({choice} {t1} {t2})"
    elif choice == 'implies':
        t1 = generate_bool_term(ctx, allow_let=False)
        t2 = generate_bool_term(ctx, allow_let=False)
        result = f"(=> {t1} {t2})"
    elif choice == 'equals':
        # Ensure type consistency for equals
        if random.choice([True, False]):
            # Boolean equality
            t1 = generate_bool_term(ctx, allow_let=False)
            t2 = generate_bool_term(ctx, allow_let=False)
        else:
            # Bitvector equality - same width
            width = random.choice([8, 16, 32])
            t1 = generate_bv_term(ctx, width, allow_let=False)
            t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"(= {t1} {t2})"
    elif choice == 'distinct':
        # Ensure type consistency for distinct
        if random.choice([True, False]):
            # Boolean distinct
            t1 = generate_bool_term(ctx, allow_let=False)
            t2 = generate_bool_term(ctx, allow_let=False)
        else:
            # Bitvector distinct - same width
            width = random.choice([8, 16, 32])
            t1 = generate_bv_term(ctx, width, allow_let=False)
            t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"(distinct {t1} {t2})"
    elif choice == 'ite':
        cond = generate_bool_term(ctx, allow_let=False)
        t1 = generate_bool_term(ctx, allow_let=False)
        t2 = generate_bool_term(ctx, allow_let=False)
        result = f"(ite {cond} {t1} {t2})"
    elif choice == 'bvult':
        # Ensure both operands have same width
        width = random.choice([8, 16, 32])
        t1 = generate_bv_term(ctx, width, allow_let=False)
        t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"(bvult {t1} {t2})"
    elif choice in ['bvuaddo', 'bvsaddo', 'bvumulo', 'bvsmulo']:
        # Overflow predicates - ensure both operands have same width
        width = random.choice([8, 16, 32])
        t1 = generate_bv_term(ctx, width, allow_let=False)
        t2 = generate_bv_term(ctx, width, allow_let=False)
        result = f"({choice} {t1} {t2})"
    else:
        result = random.choice(['true', 'false'])
    
    ctx.depth -= 1
    return result

# ============================================================================
# Main Generation Function
# ============================================================================
def generate_fixedsizebitvectors_formula_with_decls():
    """Generate a random FixedSizeBitVectors formula with declarations."""
    ctx = Context()
    
    # Pre-populate with some variables for diversity
    num_bool_vars = random.randint(0, 3)
    for _ in range(num_bool_vars):
        name = generate_name()
        ctx.add_bool_var(name)
    
    num_bv_vars = random.randint(1, 4)
    for _ in range(num_bv_vars):
        name = generate_name()
        width = random.choice([8, 16, 32])
        ctx.add_bv_var(name, width)
    
    if random.random() < 0.3:
        num_int_vars = random.randint(0, 2)
        for _ in range(num_int_vars):
            name = generate_name()
            ctx.add_int_var(name)
    
    # Generate the main formula
    formula = generate_bool_term(ctx)
    
    return ctx.get_decls(), formula