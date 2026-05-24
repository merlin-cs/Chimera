import random

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'assert', 'check-sat', 'declare-fun', 'declare-const',
    'define-fun', 'set-logic', 'set-option', 'get-model', 'exit',
    'Int', 'Bool', 'Array', 'Seq', 'as', 'distinct', 'xor', 'lambda',
    'seq', 'div', 'mod', 'abs', 'select', 'store', 'const',
}

# ============================================================================
# Random Name Generator
# ============================================================================
def generate_random_name(min_length=5, max_length=10):
    """Generate a random lowercase name that is not an SMT-LIB keyword."""
    while True:
        length = random.randint(min_length, max_length)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and depth
# ============================================================================
class Context:
    def __init__(self, max_depth=5):
        self.max_depth = max_depth
        self.bool_vars = []
        self.int_vars = []
        self.seq_vars = []
        self.elem_vars = []
        self.array_vars = []
        self.elem_sort = 'Int'  # Default element sort for sequences
        self.declarations = []
        
    def add_bool_var(self):
        name = generate_random_name()
        self.bool_vars.append(name)
        self.declarations.append(f"(declare-const {name} Bool)")
        return name
    
    def add_int_var(self):
        name = generate_random_name()
        self.int_vars.append(name)
        self.declarations.append(f"(declare-const {name} Int)")
        return name
    
    def add_seq_var(self):
        name = generate_random_name()
        self.seq_vars.append(name)
        self.declarations.append(f"(declare-const {name} (Seq {self.elem_sort}))")
        return name
    
    def add_elem_var(self):
        name = generate_random_name()
        self.elem_vars.append(name)
        self.declarations.append(f"(declare-const {name} {self.elem_sort})")
        return name
    
    def add_array_var(self, domain_sort, range_sort):
        name = generate_random_name()
        self.array_vars.append((name, domain_sort, range_sort))
        self.declarations.append(f"(declare-const {name} (Array {domain_sort} {range_sort}))")
        return name
    
    def get_decls(self):
        return '\n'.join(self.declarations)

# ============================================================================
# Term Generators
# ============================================================================

def generate_int_literal():
    """Generate a random integer literal."""
    val = random.randint(-100, 100)
    if val < 0:
        return f"(- {-val})"
    return str(val)

def generate_int_term(ctx, depth=0):
    """Generate a random integer term."""
    if depth >= ctx.max_depth:
        if ctx.int_vars and random.random() < 0.5:
            return random.choice(ctx.int_vars)
        return generate_int_literal()
    
    choices = ['literal', 'var', 'seq.len', 'arith', 'ite']
    choice = random.choice(choices)
    
    if choice == 'literal':
        return generate_int_literal()
    elif choice == 'var':
        if not ctx.int_vars or random.random() < 0.3:
            return ctx.add_int_var()
        return random.choice(ctx.int_vars)
    elif choice == 'seq.len':
        seq = generate_seq_term(ctx, depth + 1)
        return f"(seq.len {seq})"
    elif choice == 'arith':
        op = random.choice(['+', '-', '*', 'div', 'mod', 'abs'])
        if op == 'abs':
            arg = generate_int_term(ctx, depth + 1)
            return f"(abs {arg})"
        elif op == '-' and random.random() < 0.5:
            arg = generate_int_term(ctx, depth + 1)
            return f"(- {arg})"
        elif op in ['div', 'mod']:
            arg1 = generate_int_term(ctx, depth + 1)
            arg2 = generate_int_term(ctx, depth + 1)
            return f"({op} {arg1} {arg2})"
        else:
            num_args = random.randint(2, 3)
            args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
            return f"({op} {' '.join(args)})"
    else:  # ite
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_int_term(ctx, depth + 1)
        else_term = generate_int_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"

def generate_seq_term(ctx, depth=0):
    """Generate a random sequence term."""
    if depth >= ctx.max_depth:
        if ctx.seq_vars and random.random() < 0.7:
            return random.choice(ctx.seq_vars)
        return f"(as seq.empty (Seq {ctx.elem_sort}))"
    
    choices = ['var', 'empty', 'unit', 'concat', 'extract', 'ite']
    choice = random.choice(choices)
    
    if choice == 'var':
        if not ctx.seq_vars or random.random() < 0.3:
            return ctx.add_seq_var()
        return random.choice(ctx.seq_vars)
    elif choice == 'empty':
        return f"(as seq.empty (Seq {ctx.elem_sort}))"
    elif choice == 'unit':
        elem = generate_elem_term(ctx, depth + 1)
        return f"(seq.unit {elem})"
    elif choice == 'concat':
        num_args = random.randint(2, 3)
        args = [generate_seq_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(seq.++ {' '.join(args)})"
    elif choice == 'extract':
        seq = generate_seq_term(ctx, depth + 1)
        offset = generate_int_term(ctx, depth + 1)
        length = generate_int_term(ctx, depth + 1)
        return f"(seq.extract {seq} {offset} {length})"
    else:  # ite
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_seq_term(ctx, depth + 1)
        else_term = generate_seq_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"

def generate_elem_term(ctx, depth=0):
    """Generate a random element term (Int or Bool)."""
    if depth >= ctx.max_depth:
        if ctx.elem_sort == 'Int':
            if ctx.int_vars and random.random() < 0.5:
                return random.choice(ctx.int_vars)
            return generate_int_literal()
        else:
            if ctx.bool_vars and random.random() < 0.5:
                return random.choice(ctx.bool_vars)
            return random.choice(['true', 'false'])
    
    if ctx.elem_sort == 'Int':
        return generate_int_term(ctx, depth)
    else:
        return generate_bool_term(ctx, depth)

def generate_bool_term(ctx, depth=0):
    """Generate a random Boolean term."""
    if depth >= ctx.max_depth:
        if ctx.bool_vars and random.random() < 0.5:
            return random.choice(ctx.bool_vars)
        return random.choice(['true', 'false'])
    
    choices = ['literal', 'var', 'seq_pred', 'int_cmp', 'not', 'and', 'or', 
               'implies', 'xor', 'eq', 'distinct', 'ite']
    choice = random.choice(choices)
    
    if choice == 'literal':
        return random.choice(['true', 'false'])
    elif choice == 'var':
        if not ctx.bool_vars or random.random() < 0.3:
            return ctx.add_bool_var()
        return random.choice(ctx.bool_vars)
    elif choice == 'seq_pred':
        pred = random.choice(['seq.contains', 'seq.prefixof', 'seq.suffixof', '='])
        if pred == '=':
            seq1 = generate_seq_term(ctx, depth + 1)
            seq2 = generate_seq_term(ctx, depth + 1)
            return f"(= {seq1} {seq2})"
        else:
            seq1 = generate_seq_term(ctx, depth + 1)
            seq2 = generate_seq_term(ctx, depth + 1)
            return f"({pred} {seq1} {seq2})"
    elif choice == 'int_cmp':
        op = random.choice(['=', '<', '<=', '>', '>='])
        int1 = generate_int_term(ctx, depth + 1)
        int2 = generate_int_term(ctx, depth + 1)
        return f"({op} {int1} {int2})"
    elif choice == 'not':
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"
    elif choice in ['and', 'or']:
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"({choice} {' '.join(args)})"
    elif choice == 'implies':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(=> {arg1} {arg2})"
    elif choice == 'xor':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(xor {arg1} {arg2})"
    elif choice == 'eq':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(= {arg1} {arg2})"
    elif choice == 'distinct':
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(distinct {' '.join(args)})"
    else:  # ite
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_bool_term(ctx, depth + 1)
        else_term = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"

# ============================================================================
# Main Generator Function
# ============================================================================

def generate_z3seq_formula_with_decls():
    """Generate a random z3_seq formula with declarations."""
    ctx = Context(max_depth=random.randint(3, 6))
    
    # Pre-populate with some variables for diversity
    num_bool_vars = random.randint(1, 3)
    num_int_vars = random.randint(1, 3)
    num_seq_vars = random.randint(1, 3)
    
    for _ in range(num_bool_vars):
        ctx.add_bool_var()
    for _ in range(num_int_vars):
        ctx.add_int_var()
    for _ in range(num_seq_vars):
        ctx.add_seq_var()
    
    # Generate the formula
    formula = generate_bool_term(ctx, depth=0)
    
    # Get declarations
    decls = ctx.get_decls()
    
    return decls, formula