import random
import string

# ============================================================================
# Configuration and Constants
# ============================================================================

MAX_DEPTH = 6
MAX_CHILDREN = 4
MIN_CHILDREN = 2

SMT_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'let', 'forall', 'exists',
    'true', 'false', 'distinct', 'div', 'mod', 'abs', 'Int', 'Bool',
    'assert', 'check-sat', 'declare-fun', 'declare-const', 'set-logic',
    'define-fun', 'get-model', 'push', 'pop', 'exit'
}

# ============================================================================
# Symbol Generation
# ============================================================================

def generate_symbol():
    """Generate a random symbol name (>= 5 chars, lowercase, not a keyword)."""
    while True:
        length = random.randint(5, 10)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in SMT_KEYWORDS:
            return name

# ============================================================================
# Context Management
# ============================================================================

class Context:
    def __init__(self):
        self.int_vars = []
        self.bool_vars = []
        self.int_consts = []
        self.bool_consts = []
        self.scopes = []  # Stack of local bindings
        
    def push_scope(self, bindings):
        """Push a new scope with bindings: list of (name, sort)."""
        self.scopes.append(bindings)
    
    def pop_scope(self):
        """Pop the current scope."""
        if self.scopes:
            self.scopes.pop()
    
    def get_int_symbols(self):
        """Get all available int symbols (vars + consts + local bindings)."""
        symbols = self.int_vars + self.int_consts
        for scope in self.scopes:
            symbols.extend([name for name, sort in scope if sort == 'Int'])
        return symbols
    
    def get_bool_symbols(self):
        """Get all available bool symbols (vars + consts + local bindings)."""
        symbols = self.bool_vars + self.bool_consts
        for scope in self.scopes:
            symbols.extend([name for name, sort in scope if sort == 'Bool'])
        return symbols

# ============================================================================
# Integer Term Generation
# ============================================================================

def generate_int_term(ctx, depth=0):
    """Generate a random integer term."""
    if depth >= MAX_DEPTH:
        return generate_int_leaf(ctx)
    
    choices = ['numeral', 'variable', 'negation', 'binary_op', 'abs', 'ite', 'let']
    weights = [15, 20, 10, 20, 5, 10, 5]
    
    if depth >= MAX_DEPTH - 1:
        choices = ['numeral', 'variable']
        weights = [1, 1]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'numeral':
        return generate_numeral()
    elif choice == 'variable':
        return generate_int_variable(ctx)
    elif choice == 'negation':
        return f"(- {generate_int_term(ctx, depth + 1)})"
    elif choice == 'binary_op':
        return generate_int_binary_op(ctx, depth)
    elif choice == 'abs':
        return f"(abs {generate_int_term(ctx, depth + 1)})"
    elif choice == 'ite':
        return generate_int_ite(ctx, depth)
    elif choice == 'let':
        return generate_int_let(ctx, depth)
    else:
        return generate_int_leaf(ctx)

def generate_int_leaf(ctx):
    """Generate a leaf integer term (numeral or variable)."""
    int_syms = ctx.get_int_symbols()
    if int_syms and random.random() < 0.6:
        return random.choice(int_syms)
    return generate_numeral()

def generate_numeral():
    """Generate a numeral (0 or positive integer)."""
    return str(random.randint(0, 100))

def generate_int_variable(ctx):
    """Generate or reuse an integer variable."""
    int_syms = ctx.get_int_symbols()
    if int_syms and random.random() < 0.7:
        return random.choice(int_syms)
    return generate_numeral()

def generate_int_binary_op(ctx, depth):
    """Generate a binary integer operation."""
    ops = ['+', '-', '*', 'div', 'mod']
    op = random.choice(ops)
    
    if op == 'mod':
        # mod is binary only
        t1 = generate_int_term(ctx, depth + 1)
        t2 = generate_int_term(ctx, depth + 1)
        return f"({op} {t1} {t2})"
    else:
        # Other ops can have 2+ arguments
        num_args = random.randint(MIN_CHILDREN, MAX_CHILDREN)
        args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"

def generate_int_ite(ctx, depth):
    """Generate an integer if-then-else."""
    cond = generate_bool_term(ctx, depth + 1)
    then_term = generate_int_term(ctx, depth + 1)
    else_term = generate_int_term(ctx, depth + 1)
    return f"(ite {cond} {then_term} {else_term})"

def generate_int_let(ctx, depth):
    """Generate an integer let binding."""
    num_bindings = random.randint(1, 3)
    bindings = []
    binding_strs = []
    
    for _ in range(num_bindings):
        name = generate_symbol()
        sort = random.choice(['Int', 'Bool'])
        if sort == 'Int':
            value = generate_int_term(ctx, depth + 1)
        else:
            value = generate_bool_term(ctx, depth + 1)
        bindings.append((name, sort))
        binding_strs.append(f"({name} {value})")
    
    ctx.push_scope(bindings)
    body = generate_int_term(ctx, depth + 1)
    ctx.pop_scope()
    
    return f"(let ({' '.join(binding_strs)}) {body})"

# ============================================================================
# Boolean Term Generation
# ============================================================================

def generate_bool_term(ctx, depth=0):
    """Generate a random boolean term."""
    if depth >= MAX_DEPTH:
        return generate_bool_leaf(ctx)
    
    choices = [
        'literal', 'variable', 'comparison', 'divisible', 'negation',
        'binary_op', 'ite', 'let', 'quantifier', 'equality', 'distinct'
    ]
    weights = [10, 15, 15, 5, 10, 15, 8, 5, 5, 8, 4]
    
    if depth >= MAX_DEPTH - 1:
        choices = ['literal', 'variable', 'comparison', 'equality']
        weights = [1, 1, 1, 1]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'literal':
        return random.choice(['true', 'false'])
    elif choice == 'variable':
        return generate_bool_variable(ctx)
    elif choice == 'comparison':
        return generate_comparison(ctx, depth)
    elif choice == 'divisible':
        return generate_divisible(ctx, depth)
    elif choice == 'negation':
        return f"(not {generate_bool_term(ctx, depth + 1)})"
    elif choice == 'binary_op':
        return generate_bool_binary_op(ctx, depth)
    elif choice == 'ite':
        return generate_bool_ite(ctx, depth)
    elif choice == 'let':
        return generate_bool_let(ctx, depth)
    elif choice == 'quantifier':
        return generate_quantifier(ctx, depth)
    elif choice == 'equality':
        return generate_equality(ctx, depth)
    elif choice == 'distinct':
        return generate_distinct(ctx, depth)
    else:
        return generate_bool_leaf(ctx)

def generate_bool_leaf(ctx):
    """Generate a leaf boolean term."""
    bool_syms = ctx.get_bool_symbols()
    if bool_syms and random.random() < 0.5:
        return random.choice(bool_syms)
    return random.choice(['true', 'false'])

def generate_bool_variable(ctx):
    """Generate or reuse a boolean variable."""
    bool_syms = ctx.get_bool_symbols()
    if bool_syms and random.random() < 0.7:
        return random.choice(bool_syms)
    return random.choice(['true', 'false'])

def generate_comparison(ctx, depth):
    """Generate a comparison operation."""
    ops = ['<=', '<', '>=', '>']
    op = random.choice(ops)
    num_args = random.randint(MIN_CHILDREN, MAX_CHILDREN)
    args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
    return f"({op} {' '.join(args)})"

def generate_divisible(ctx, depth):
    """Generate a divisibility predicate."""
    n = random.randint(1, 20)
    term = generate_int_term(ctx, depth + 1)
    return f"((_ divisible {n}) {term})"

def generate_bool_binary_op(ctx, depth):
    """Generate a boolean binary operation."""
    ops = ['and', 'or', 'xor', '=>']
    op = random.choice(ops)
    num_args = random.randint(MIN_CHILDREN, MAX_CHILDREN)
    args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
    return f"({op} {' '.join(args)})"

def generate_bool_ite(ctx, depth):
    """Generate a boolean if-then-else."""
    cond = generate_bool_term(ctx, depth + 1)
    then_term = generate_bool_term(ctx, depth + 1)
    else_term = generate_bool_term(ctx, depth + 1)
    return f"(ite {cond} {then_term} {else_term})"

def generate_bool_let(ctx, depth):
    """Generate a boolean let binding."""
    num_bindings = random.randint(1, 3)
    bindings = []
    binding_strs = []
    
    for _ in range(num_bindings):
        name = generate_symbol()
        sort = random.choice(['Int', 'Bool'])
        if sort == 'Int':
            value = generate_int_term(ctx, depth + 1)
        else:
            value = generate_bool_term(ctx, depth + 1)
        bindings.append((name, sort))
        binding_strs.append(f"({name} {value})")
    
    ctx.push_scope(bindings)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_scope()
    
    return f"(let ({' '.join(binding_strs)}) {body})"

def generate_quantifier(ctx, depth):
    """Generate a quantified formula."""
    quantifier = random.choice(['forall', 'exists'])
    num_vars = random.randint(1, 3)
    vars_list = []
    bindings = []
    
    for _ in range(num_vars):
        var_name = generate_symbol()
        vars_list.append(f"({var_name} Int)")
        bindings.append((var_name, 'Int'))
    
    ctx.push_scope(bindings)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_scope()
    
    return f"({quantifier} ({' '.join(vars_list)}) {body})"

def generate_equality(ctx, depth):
    """Generate an equality between integer terms."""
    t1 = generate_int_term(ctx, depth + 1)
    t2 = generate_int_term(ctx, depth + 1)
    return f"(= {t1} {t2})"

def generate_distinct(ctx, depth):
    """Generate a distinct predicate."""
    num_args = random.randint(MIN_CHILDREN, MAX_CHILDREN)
    args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
    return f"(distinct {' '.join(args)})"

# ============================================================================
# Declaration Generation
# ============================================================================

def generate_declarations(ctx):
    """Generate SMT-LIB2 declarations for all symbols in context."""
    decls = []
    
    for var in ctx.int_vars:
        decls.append(f"(declare-const {var} Int)")
    
    for var in ctx.bool_vars:
        decls.append(f"(declare-const {var} Bool)")
    
    for const in ctx.int_consts:
        decls.append(f"(declare-const {const} Int)")
    
    for const in ctx.bool_consts:
        decls.append(f"(declare-const {const} Bool)")
    
    return '\n'.join(decls)

# ============================================================================
# Main Generation Function
# ============================================================================

def generate_ints_formula_with_decls():
    """Generate a random SMT-LIB2 formula in the Ints theory with declarations."""
    ctx = Context()
    
    # Generate some variables and constants
    num_int_vars = random.randint(2, 6)
    num_bool_vars = random.randint(1, 4)
    
    for _ in range(num_int_vars):
        ctx.int_vars.append(generate_symbol())
    
    for _ in range(num_bool_vars):
        ctx.bool_vars.append(generate_symbol())
    
    # Optionally add some constants
    if random.random() < 0.3:
        num_int_consts = random.randint(0, 2)
        for _ in range(num_int_consts):
            ctx.int_consts.append(generate_symbol())
    
    if random.random() < 0.3:
        num_bool_consts = random.randint(0, 2)
        for _ in range(num_bool_consts):
            ctx.bool_consts.append(generate_symbol())
    
    # Generate the formula
    formula = generate_bool_term(ctx, depth=0)
    
    # Generate declarations
    decls = generate_declarations(ctx)
    
    return decls, formula