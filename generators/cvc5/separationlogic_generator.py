import random

# ============================================================================
# SMT-LIB Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'match', 'par', 'assert', 'declare-fun', 'declare-const',
    'declare-sort', 'define-fun', 'define-sort', 'set-logic', 'set-option',
    'check-sat', 'get-model', 'push', 'pop', 'as', 'sep', 'pto', 'wand',
    'emp', 'nil', 'Int', 'Bool', 'Real', 'Array', 'BitVec', 'xor',
    'distinct', 'to_real', 'to_int', 'is_int', 'mod', 'abs', 'div'
}

# ============================================================================
# Random name generation
# ============================================================================
def random_name(min_len=5):
    """Generate a random lowercase ASCII name of at least min_len chars."""
    length = random.randint(min_len, min_len + 5)
    while True:
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations
# ============================================================================
class Context:
    def __init__(self):
        self.sorts = []
        self.loc_sort = None
        self.data_sort = None
        self.constants = {}
        self.functions = {}
        self.predicates = {}
        self.depth_limit = random.randint(3, 6)
        
    def add_sort(self, name):
        self.sorts.append(name)
        
    def add_constant(self, name, sort):
        self.constants[name] = sort
        
    def add_function(self, name, arg_sorts, ret_sort):
        self.functions[name] = (arg_sorts, ret_sort)
        
    def add_predicate(self, name, arg_sorts):
        self.predicates[name] = arg_sorts
        
    def get_declarations(self):
        decls = []
        for sort_name in self.sorts:
            decls.append(f"(declare-sort {sort_name} 0)")
        decls.append(f"(declare-heap ({self.loc_sort} {self.data_sort}))")
        for const_name, sort in self.constants.items():
            decls.append(f"(declare-const {const_name} {sort})")
        for func_name, (arg_sorts, ret_sort) in self.functions.items():
            args_str = ' '.join(arg_sorts)
            decls.append(f"(declare-fun {func_name} ({args_str}) {ret_sort})")
        for pred_name, arg_sorts in self.predicates.items():
            args_str = ' '.join(arg_sorts)
            decls.append(f"(declare-fun {pred_name} ({args_str}) Bool)")
        return '\n'.join(decls)

# ============================================================================
# Initialize context with random sorts, constants, functions
# ============================================================================
def initialize_context():
    ctx = Context()
    
    # Create location and data sorts
    ctx.loc_sort = random_name()
    ctx.data_sort = random_name()
    ctx.add_sort(ctx.loc_sort)
    ctx.add_sort(ctx.data_sort)
    
    # Add Int sort for background theory
    num_int_consts = random.randint(2, 5)
    for _ in range(num_int_consts):
        ctx.add_constant(random_name(), "Int")
    
    # Add location constants
    num_loc_consts = random.randint(2, 4)
    for _ in range(num_loc_consts):
        ctx.add_constant(random_name(), ctx.loc_sort)
    
    # Add data constants
    num_data_consts = random.randint(2, 4)
    for _ in range(num_data_consts):
        ctx.add_constant(random_name(), ctx.data_sort)
    
    # Add location functions
    num_loc_funcs = random.randint(1, 3)
    for _ in range(num_loc_funcs):
        arity = random.randint(1, 2)
        arg_sorts = [ctx.loc_sort for _ in range(arity)]
        ctx.add_function(random_name(), arg_sorts, ctx.loc_sort)
    
    # Add data functions
    num_data_funcs = random.randint(1, 3)
    for _ in range(num_data_funcs):
        arity = random.randint(1, 2)
        arg_sorts = [ctx.data_sort for _ in range(arity)]
        ctx.add_function(random_name(), arg_sorts, ctx.data_sort)
    
    # Add Int functions
    num_int_funcs = random.randint(1, 2)
    for _ in range(num_int_funcs):
        arity = random.randint(1, 2)
        arg_sorts = ["Int" for _ in range(arity)]
        ctx.add_function(random_name(), arg_sorts, "Int")
    
    # Add predicates
    num_preds = random.randint(1, 3)
    for _ in range(num_preds):
        arity = random.randint(0, 2)
        if arity == 0:
            arg_sorts = []
        else:
            arg_sorts = [random.choice([ctx.loc_sort, ctx.data_sort, "Int"]) for _ in range(arity)]
        ctx.add_predicate(random_name(), arg_sorts)
    
    return ctx

# ============================================================================
# Term generation
# ============================================================================
def generate_term(ctx, sort, depth=0):
    """Generate a term of the given sort."""
    if depth > ctx.depth_limit:
        # Base case: use a constant
        candidates = [name for name, s in ctx.constants.items() if s == sort]
        if candidates:
            return random.choice(candidates)
        return "0" if sort == "Int" else random.choice(list(ctx.constants.keys()))
    
    choices = []
    
    # Constants
    const_candidates = [name for name, s in ctx.constants.items() if s == sort]
    if const_candidates:
        choices.extend([('const', c) for c in const_candidates])
    
    # Numerals for Int
    if sort == "Int":
        choices.append(('numeral', random.randint(0, 100)))
    
    # sep.nil for location sort
    if sort == ctx.loc_sort:
        choices.append(('sepnil', None))
    
    # Function applications
    func_candidates = [name for name, (args, ret) in ctx.functions.items() if ret == sort]
    if func_candidates and depth < ctx.depth_limit:
        choices.extend([('func', f) for f in func_candidates])
    
    if not choices:
        # Fallback
        if sort == "Int":
            return str(random.randint(0, 100))
        candidates = [name for name, s in ctx.constants.items() if s == sort]
        return random.choice(candidates) if candidates else random.choice(list(ctx.constants.keys()))
    
    choice_type, value = random.choice(choices)
    
    if choice_type == 'const':
        return value
    elif choice_type == 'numeral':
        return str(value)
    elif choice_type == 'sepnil':
        return f"(as sep.nil {ctx.loc_sort})"
    elif choice_type == 'func':
        arg_sorts, _ = ctx.functions[value]
        args = [generate_term(ctx, s, depth + 1) for s in arg_sorts]
        return f"({value} {' '.join(args)})"
    
    return "0"

def generate_loc_term(ctx, depth=0):
    return generate_term(ctx, ctx.loc_sort, depth)

def generate_data_term(ctx, depth=0):
    return generate_term(ctx, ctx.data_sort, depth)

def generate_int_term(ctx, depth=0):
    return generate_term(ctx, "Int", depth)

# ============================================================================
# Background literal generation
# ============================================================================
def generate_background_literal(ctx, depth=0):
    """Generate a background theory literal (Bool)."""
    choice = random.choice(['equality', 'comparison', 'predicate'])
    
    if choice == 'equality':
        sort = random.choice([ctx.loc_sort, ctx.data_sort, "Int"])
        t1 = generate_term(ctx, sort, depth)
        t2 = generate_term(ctx, sort, depth)
        return f"(= {t1} {t2})"
    
    elif choice == 'comparison':
        op = random.choice(['<', '<=', '>', '>='])
        t1 = generate_int_term(ctx, depth)
        t2 = generate_int_term(ctx, depth)
        return f"({op} {t1} {t2})"
    
    else:  # predicate
        if not ctx.predicates:
            # Fallback to equality
            sort = random.choice([ctx.loc_sort, ctx.data_sort, "Int"])
            t1 = generate_term(ctx, sort, depth)
            t2 = generate_term(ctx, sort, depth)
            return f"(= {t1} {t2})"
        pred_name = random.choice(list(ctx.predicates.keys()))
        arg_sorts = ctx.predicates[pred_name]
        if not arg_sorts:
            return pred_name
        args = [generate_term(ctx, s, depth) for s in arg_sorts]
        return f"({pred_name} {' '.join(args)})"

# ============================================================================
# SL formula generation
# ============================================================================
def generate_sl_formula(ctx, depth=0):
    """Generate a separation logic formula."""
    if depth > ctx.depth_limit:
        return "sep.emp"
    
    choice = random.choice(['sep.emp', 'pto', 'sep', 'wand'])
    
    if choice == 'sep.emp':
        return "sep.emp"
    
    elif choice == 'pto':
        loc = generate_loc_term(ctx, depth)
        data = generate_data_term(ctx, depth)
        return f"(pto {loc} {data})"
    
    elif choice == 'sep':
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(sep {' '.join(args)})"
    
    else:  # wand
        left = generate_bool_term(ctx, depth + 1)
        right = generate_bool_term(ctx, depth + 1)
        return f"(wand {left} {right})"

# ============================================================================
# Boolean term generation (main entry point)
# ============================================================================
def generate_bool_term(ctx, depth=0):
    """Generate a Boolean term following the CFG."""
    if depth > ctx.depth_limit:
        # Base case: use a simple literal or SL formula
        return random.choice([
            "sep.emp",
            generate_background_literal(ctx, depth),
            f"(pto {generate_loc_term(ctx, depth)} {generate_data_term(ctx, depth)})"
        ])
    
    # Choose production
    weights = [0.25, 0.25, 0.15, 0.35]  # sl_formula, background, not, bool_op
    choice = random.choices(['sl_formula', 'background', 'not', 'bool_op'], weights=weights)[0]
    
    if choice == 'sl_formula':
        return generate_sl_formula(ctx, depth)
    
    elif choice == 'background':
        return generate_background_literal(ctx, depth)
    
    elif choice == 'not':
        inner = generate_bool_term(ctx, depth + 1)
        return f"(not {inner})"
    
    else:  # bool_op
        op = random.choice(['and', 'or', '=>', 'xor', '='])
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"

# ============================================================================
# Main public function
# ============================================================================
def generate_separationlogic_formula_with_decls():
    """
    Generate a random Separation Logic formula with declarations.
    
    Returns:
        (decls, formula): A tuple where decls is the SMT-LIB2 declarations
                         and formula is a Boolean term.
    """
    ctx = initialize_context()
    formula = generate_bool_term(ctx, depth=0)
    decls = ctx.get_declarations()
    return decls, formula