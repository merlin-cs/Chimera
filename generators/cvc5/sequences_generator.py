import random

# ============================================================================
# SMT-LIB2 Keywords (reserved words to avoid in generated names)
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'let', 'forall', 'exists',
    'assert', 'check-sat', 'declare-const', 'declare-fun', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'as', 'distinct', 'Int', 'Bool', 'Seq', 'BitVec', 'seq', 'bv',
    'div', 'mod', 'abs', 'seq.empty', 'seq.unit', 'seq.len', 'seq.nth',
    'seq.update', 'seq.extract', 'seq.at', 'seq.contains', 'seq.indexof',
    'seq.replace', 'seq.replace_all', 'seq.rev', 'seq.prefixof', 'seq.suffixof',
    'bvadd', 'bvsub', 'bvmul', 'bvnot', 'bvand', 'bvor'
}

# ============================================================================
# Name Generation
# ============================================================================
def generate_name(min_len=5, max_len=12):
    """Generate a random lowercase name (>= min_len chars) that is not a keyword."""
    while True:
        length = random.randint(min_len, max_len)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and types
# ============================================================================
class Context:
    def __init__(self):
        self.bool_vars = []
        self.int_vars = []
        self.seq_int_vars = []
        self.bv_widths = [4, 8, 16, 32]
        self.bv_vars_by_width = {w: [] for w in self.bv_widths}
        self.seq_bv_vars_by_width = {w: [] for w in self.bv_widths}
        self.decls = []
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
        self.decls.append(f"(declare-const {name} Bool)")
        
    def add_int_var(self, name):
        self.int_vars.append(name)
        self.decls.append(f"(declare-const {name} Int)")
        
    def add_seq_int_var(self, name):
        self.seq_int_vars.append(name)
        self.decls.append(f"(declare-const {name} (Seq Int))")
        
    def add_bv_var(self, name, width):
        self.bv_vars_by_width[width].append(name)
        self.decls.append(f"(declare-const {name} (_ BitVec {width}))")
        
    def add_seq_bv_var(self, name, width):
        self.seq_bv_vars_by_width[width].append(name)
        self.decls.append(f"(declare-const {name} (Seq (_ BitVec {width})))")
        
    def get_decls(self):
        return '\n'.join(self.decls)

# ============================================================================
# Initialize context with random variables
# ============================================================================
def init_context():
    ctx = Context()
    num_bool = random.randint(1, 4)
    num_int = random.randint(2, 5)
    num_seq_int = random.randint(2, 5)
    
    for _ in range(num_bool):
        ctx.add_bool_var(generate_name())
    for _ in range(num_int):
        ctx.add_int_var(generate_name())
    for _ in range(num_seq_int):
        ctx.add_seq_int_var(generate_name())
    
    # Add some bitvector variables
    if random.random() < 0.6:
        num_bv = random.randint(1, 3)
        for _ in range(num_bv):
            width = random.choice(ctx.bv_widths)
            ctx.add_bv_var(generate_name(), width)
    
    # Add some sequence of bitvector variables
    if random.random() < 0.5:
        num_seq_bv = random.randint(1, 3)
        for _ in range(num_seq_bv):
            width = random.choice(ctx.bv_widths)
            ctx.add_seq_bv_var(generate_name(), width)
    
    return ctx

# ============================================================================
# Term Generation (CFG-based)
# ============================================================================
MAX_DEPTH = 6

def gen_bool_term(ctx, depth=0):
    """Generate a BoolTerm following the CFG."""
    if depth >= MAX_DEPTH:
        return gen_bool_atom(ctx)
    
    choices = [
        'atom', 'not', 'and', 'or', 'implies', 'xor', 'ite',
        'eq', 'distinct', 'seq_bool_op', 'int_bool_op'
    ]
    weights = [15, 8, 10, 10, 5, 5, 6, 10, 5, 12, 10]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'atom':
        return gen_bool_atom(ctx)
    elif choice == 'not':
        return f"(not {gen_bool_term(ctx, depth+1)})"
    elif choice == 'and':
        n = random.randint(2, 3)
        args = ' '.join(gen_bool_term(ctx, depth+1) for _ in range(n))
        return f"(and {args})"
    elif choice == 'or':
        n = random.randint(2, 3)
        args = ' '.join(gen_bool_term(ctx, depth+1) for _ in range(n))
        return f"(or {args})"
    elif choice == 'implies':
        return f"(=> {gen_bool_term(ctx, depth+1)} {gen_bool_term(ctx, depth+1)})"
    elif choice == 'xor':
        return f"(xor {gen_bool_term(ctx, depth+1)} {gen_bool_term(ctx, depth+1)})"
    elif choice == 'ite':
        return f"(ite {gen_bool_term(ctx, depth+1)} {gen_bool_term(ctx, depth+1)} {gen_bool_term(ctx, depth+1)})"
    elif choice == 'eq':
        sort_choice = random.choice(['bool', 'int', 'seq_int'])
        if sort_choice == 'bool':
            return f"(= {gen_bool_term(ctx, depth+1)} {gen_bool_term(ctx, depth+1)})"
        elif sort_choice == 'int':
            return f"(= {gen_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
        else:
            return f"(= {gen_seq_int_term(ctx, depth+1)} {gen_seq_int_term(ctx, depth+1)})"
    elif choice == 'distinct':
        sort_choice = random.choice(['int', 'seq_int'])
        if sort_choice == 'int':
            n = random.randint(2, 3)
            args = ' '.join(gen_int_term(ctx, depth+1) for _ in range(n))
            return f"(distinct {args})"
        else:
            n = random.randint(2, 3)
            args = ' '.join(gen_seq_int_term(ctx, depth+1) for _ in range(n))
            return f"(distinct {args})"
    elif choice == 'seq_bool_op':
        return gen_seq_bool_op(ctx, depth+1)
    elif choice == 'int_bool_op':
        return gen_int_bool_op(ctx, depth+1)
    else:
        return gen_bool_atom(ctx)

def gen_bool_atom(ctx):
    """Generate a BoolAtom: true, false, or a Boolean variable."""
    if ctx.bool_vars and random.random() < 0.6:
        return random.choice(ctx.bool_vars)
    return random.choice(['true', 'false'])

def gen_seq_bool_op(ctx, depth):
    """Generate a Boolean-returning sequence operation."""
    op = random.choice(['seq.contains', 'seq.prefixof', 'seq.suffixof'])
    s1 = gen_seq_int_term(ctx, depth)
    s2 = gen_seq_int_term(ctx, depth)
    return f"({op} {s1} {s2})"

def gen_int_bool_op(ctx, depth):
    """Generate an integer comparison."""
    op = random.choice(['<', '<=', '>', '>='])
    i1 = gen_int_term(ctx, depth)
    i2 = gen_int_term(ctx, depth)
    return f"({op} {i1} {i2})"

def gen_int_term(ctx, depth=0):
    """Generate an IntTerm."""
    if depth >= MAX_DEPTH:
        if ctx.int_vars and random.random() < 0.7:
            return random.choice(ctx.int_vars)
        return str(random.randint(0, 20))
    
    choices = ['literal', 'var', 'add', 'sub', 'mul', 'div', 'mod', 'abs', 'seq.len', 'seq.indexof', 'ite']
    weights = [10, 15, 8, 6, 6, 4, 4, 3, 10, 5, 4]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'literal':
        return str(random.randint(0, 20))
    elif choice == 'var':
        if ctx.int_vars:
            return random.choice(ctx.int_vars)
        return str(random.randint(0, 10))
    elif choice == 'add':
        n = random.randint(2, 3)
        args = ' '.join(gen_int_term(ctx, depth+1) for _ in range(n))
        return f"(+ {args})"
    elif choice == 'sub':
        if random.random() < 0.5:
            return f"(- {gen_int_term(ctx, depth+1)})"
        else:
            return f"(- {gen_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
    elif choice == 'mul':
        n = random.randint(2, 3)
        args = ' '.join(gen_int_term(ctx, depth+1) for _ in range(n))
        return f"(* {args})"
    elif choice == 'div':
        return f"(div {gen_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
    elif choice == 'mod':
        return f"(mod {gen_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
    elif choice == 'abs':
        return f"(abs {gen_int_term(ctx, depth+1)})"
    elif choice == 'seq.len':
        return f"(seq.len {gen_seq_int_term(ctx, depth+1)})"
    elif choice == 'seq.indexof':
        s1 = gen_seq_int_term(ctx, depth+1)
        s2 = gen_seq_int_term(ctx, depth+1)
        i = gen_int_term(ctx, depth+1)
        return f"(seq.indexof {s1} {s2} {i})"
    elif choice == 'ite':
        return f"(ite {gen_bool_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
    else:
        return str(random.randint(0, 10))

def gen_seq_int_term(ctx, depth=0):
    """Generate a SeqTerm with element sort Int."""
    if depth >= MAX_DEPTH:
        if ctx.seq_int_vars:
            return random.choice(ctx.seq_int_vars)
        return "(as seq.empty (Seq Int))"
    
    choices = ['var', 'empty', 'unit', 'concat', 'at', 'extract', 'update', 'replace', 'replace_all', 'rev', 'ite']
    weights = [20, 5, 10, 10, 6, 8, 6, 5, 4, 5, 4]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'var':
        if ctx.seq_int_vars:
            return random.choice(ctx.seq_int_vars)
        return "(as seq.empty (Seq Int))"
    elif choice == 'empty':
        return "(as seq.empty (Seq Int))"
    elif choice == 'unit':
        return f"(seq.unit {gen_int_term(ctx, depth+1)})"
    elif choice == 'concat':
        n = random.randint(2, 3)
        args = ' '.join(gen_seq_int_term(ctx, depth+1) for _ in range(n))
        return f"(seq.++ {args})"
    elif choice == 'at':
        return f"(seq.at {gen_seq_int_term(ctx, depth+1)} {gen_int_term(ctx, depth+1)})"
    elif choice == 'extract':
        s = gen_seq_int_term(ctx, depth+1)
        i1 = gen_int_term(ctx, depth+1)
        i2 = gen_int_term(ctx, depth+1)
        return f"(seq.extract {s} {i1} {i2})"
    elif choice == 'update':
        s1 = gen_seq_int_term(ctx, depth+1)
        i = gen_int_term(ctx, depth+1)
        s2 = gen_seq_int_term(ctx, depth+1)
        return f"(seq.update {s1} {i} {s2})"
    elif choice == 'replace':
        s1 = gen_seq_int_term(ctx, depth+1)
        s2 = gen_seq_int_term(ctx, depth+1)
        s3 = gen_seq_int_term(ctx, depth+1)
        return f"(seq.replace {s1} {s2} {s3})"
    elif choice == 'replace_all':
        s1 = gen_seq_int_term(ctx, depth+1)
        s2 = gen_seq_int_term(ctx, depth+1)
        s3 = gen_seq_int_term(ctx, depth+1)
        return f"(seq.replace_all {s1} {s2} {s3})"
    elif choice == 'rev':
        return f"(seq.rev {gen_seq_int_term(ctx, depth+1)})"
    elif choice == 'ite':
        return f"(ite {gen_bool_term(ctx, depth+1)} {gen_seq_int_term(ctx, depth+1)} {gen_seq_int_term(ctx, depth+1)})"
    else:
        if ctx.seq_int_vars:
            return random.choice(ctx.seq_int_vars)
        return "(as seq.empty (Seq Int))"

# ============================================================================
# Main entry point
# ============================================================================
def generate_sequences_formula_with_decls():
    ctx = init_context()
    formula = gen_bool_term(ctx, depth=0)
    decls = ctx.get_decls()
    return decls, formula