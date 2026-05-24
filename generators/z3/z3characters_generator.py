import random
import string

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'assert', 'check-sat', 'declare-fun', 'declare-const', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'Bool', 'Int', 'Real', 'String', 'Array', 'BitVec', 'distinct', 'Char',
    'Unicode', 'char', 'to_int', 'is_digit'
}

# ============================================================================
# Random Name Generation
# ============================================================================
def generate_random_name(min_length=5, max_length=12):
    """Generate a random lowercase name that is not an SMT-LIB keyword."""
    while True:
        length = random.randint(min_length, max_length)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and variables
# ============================================================================
class GenerationContext:
    def __init__(self):
        self.bool_vars = []
        self.char_vars = []
        self.int_vars = []
        self.bool_funcs = []  # (name, arity)
        self.char_funcs = []  # (name, arity)
        self.int_funcs = []   # (name, arity)
        self.max_depth = random.randint(3, 6)
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
    
    def add_char_var(self, name):
        self.char_vars.append(name)
    
    def add_int_var(self, name):
        self.int_vars.append(name)
    
    def add_bool_func(self, name, arity):
        self.bool_funcs.append((name, arity))
    
    def add_char_func(self, name, arity):
        self.char_funcs.append((name, arity))
    
    def add_int_func(self, name, arity):
        self.int_funcs.append((name, arity))
    
    def get_declarations(self):
        decls = []
        for var in self.bool_vars:
            decls.append(f"(declare-const {var} Bool)")
        for var in self.char_vars:
            decls.append(f"(declare-const {var} (_ BitVec 32))")
        for var in self.int_vars:
            decls.append(f"(declare-const {var} Int)")
        for name, arity in self.bool_funcs:
            if arity == 0:
                decls.append(f"(declare-const {name} Bool)")
            else:
                args = " ".join(["Bool"] * arity)
                decls.append(f"(declare-fun {name} ({args}) Bool)")
        for name, arity in self.char_funcs:
            if arity == 0:
                decls.append(f"(declare-const {name} (_ BitVec 32))")
            else:
                args = " ".join(["(_ BitVec 32)"] * arity)
                decls.append(f"(declare-fun {name} ({args}) (_ BitVec 32))")
        for name, arity in self.int_funcs:
            if arity == 0:
                decls.append(f"(declare-const {name} Int)")
            else:
                args = " ".join(["Int"] * arity)
                decls.append(f"(declare-fun {name} ({args}) Int)")
        return "\n".join(decls)

# ============================================================================
# Initialize context with random variables and functions
# ============================================================================
def initialize_context():
    ctx = GenerationContext()
    
    # Add random number of variables
    num_bool_vars = random.randint(1, 4)
    num_char_vars = random.randint(1, 4)
    num_int_vars = random.randint(0, 3)
    
    for _ in range(num_bool_vars):
        ctx.add_bool_var(generate_random_name())
    for _ in range(num_char_vars):
        ctx.add_char_var(generate_random_name())
    for _ in range(num_int_vars):
        ctx.add_int_var(generate_random_name())
    
    # Add random functions
    if random.random() < 0.4:
        arity = random.randint(0, 2)
        ctx.add_bool_func(generate_random_name(), arity)
    if random.random() < 0.3:
        arity = random.randint(0, 2)
        ctx.add_char_func(generate_random_name(), arity)
    if random.random() < 0.2:
        arity = random.randint(0, 2)
        ctx.add_int_func(generate_random_name(), arity)
    
    return ctx

# ============================================================================
# Character Term Generation
# ============================================================================
def generate_char_literal():
    """Generate a character literal (_ Char n) where n is a code point."""
    # Use common ASCII range mostly, occasionally go higher
    if random.random() < 0.8:
        code_point = random.randint(32, 126)  # Printable ASCII
    else:
        code_point = random.randint(0, 1000)
    return f"(_ BitVec 32) #x{code_point:08x}"

def generate_char_term(ctx, depth):
    """Generate a character term."""
    if depth >= ctx.max_depth:
        # Force terminal
        if ctx.char_vars and random.random() < 0.7:
            return random.choice(ctx.char_vars)
        else:
            code_point = random.randint(32, 126)
            return f"#x{code_point:08x}"
    
    choices = ['literal', 'variable']
    if ctx.char_funcs:
        choices.append('function')
    
    choice = random.choice(choices)
    
    if choice == 'literal':
        code_point = random.randint(32, 126)
        return f"#x{code_point:08x}"
    elif choice == 'variable':
        if ctx.char_vars:
            return random.choice(ctx.char_vars)
        else:
            code_point = random.randint(32, 126)
            return f"#x{code_point:08x}"
    else:  # function
        name, arity = random.choice(ctx.char_funcs)
        if arity == 0:
            return name
        else:
            args = [generate_char_term(ctx, depth + 1) for _ in range(arity)]
            return f"({name} {' '.join(args)})"

# ============================================================================
# Integer Term Generation
# ============================================================================
def generate_int_term(ctx, depth):
    """Generate an integer term."""
    if depth >= ctx.max_depth:
        # Force terminal
        if ctx.int_vars and random.random() < 0.5:
            return random.choice(ctx.int_vars)
        else:
            return str(random.randint(0, 100))
    
    choices = ['numeral']
    if ctx.int_vars:
        choices.append('variable')
    if ctx.int_funcs:
        choices.append('function')
    choices.append('char_to_int')
    if depth < ctx.max_depth - 1:
        choices.append('ite')
    
    choice = random.choice(choices)
    
    if choice == 'numeral':
        return str(random.randint(0, 100))
    elif choice == 'variable':
        return random.choice(ctx.int_vars)
    elif choice == 'function':
        name, arity = random.choice(ctx.int_funcs)
        if arity == 0:
            return name
        else:
            args = [generate_int_term(ctx, depth + 1) for _ in range(arity)]
            return f"({name} {' '.join(args)})"
    elif choice == 'char_to_int':
        char_term = generate_char_term(ctx, depth + 1)
        return f"(bv2int {char_term})"
    else:  # ite
        bool_term = generate_bool_term(ctx, depth + 1)
        then_term = generate_int_term(ctx, depth + 1)
        else_term = generate_int_term(ctx, depth + 1)
        return f"(ite {bool_term} {then_term} {else_term})"

# ============================================================================
# Boolean Term Generation
# ============================================================================
def generate_bool_term(ctx, depth):
    """Generate a boolean term following the CFG."""
    if depth >= ctx.max_depth:
        # Force terminal production
        choices = ['literal']
        if ctx.bool_vars:
            choices.append('variable')
        choice = random.choice(choices)
        if choice == 'literal':
            return random.choice(['true', 'false'])
        else:
            return random.choice(ctx.bool_vars)
    
    # Build list of possible productions with weights
    productions = []
    weights = []
    
    # Literals
    productions.append('literal')
    weights.append(5)
    
    # Variables
    if ctx.bool_vars:
        productions.append('variable')
        weights.append(10)
    
    # Function applications
    if ctx.bool_funcs:
        productions.append('function')
        weights.append(5)
    
    # Character comparisons
    productions.extend(['char_le', 'char_eq', 'char_distinct'])
    weights.extend([8, 8, 6])
    
    # Character predicates
    productions.append('char_is_digit')
    weights.append(7)
    
    # Boolean operators
    productions.extend(['not', 'and', 'or', 'xor', 'implies', 'bool_eq', 'bool_distinct', 'ite'])
    weights.extend([10, 12, 12, 6, 8, 6, 5, 8])
    
    production = random.choices(productions, weights=weights)[0]
    
    if production == 'literal':
        return random.choice(['true', 'false'])
    
    elif production == 'variable':
        return random.choice(ctx.bool_vars)
    
    elif production == 'function':
        name, arity = random.choice(ctx.bool_funcs)
        if arity == 0:
            return name
        else:
            args = [generate_bool_term(ctx, depth + 1) for _ in range(arity)]
            return f"({name} {' '.join(args)})"
    
    elif production == 'char_le':
        char1 = generate_char_term(ctx, depth + 1)
        char2 = generate_char_term(ctx, depth + 1)
        return f"(bvule {char1} {char2})"
    
    elif production == 'char_eq':
        char1 = generate_char_term(ctx, depth + 1)
        char2 = generate_char_term(ctx, depth + 1)
        return f"(= {char1} {char2})"
    
    elif production == 'char_distinct':
        num_terms = random.randint(2, 3)
        chars = [generate_char_term(ctx, depth + 1) for _ in range(num_terms)]
        return f"(distinct {' '.join(chars)})"
    
    elif production == 'char_is_digit':
        char_term = generate_char_term(ctx, depth + 1)
        # char.is_digit checks if char is in range '0' to '9' (48-57)
        return f"(and (bvule #x00000030 {char_term}) (bvule {char_term} #x00000039))"
    
    elif production == 'not':
        inner = generate_bool_term(ctx, depth + 1)
        return f"(not {inner})"
    
    elif production == 'and':
        num_terms = random.randint(2, 4)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(num_terms)]
        return f"(and {' '.join(terms)})"
    
    elif production == 'or':
        num_terms = random.randint(2, 4)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(num_terms)]
        return f"(or {' '.join(terms)})"
    
    elif production == 'xor':
        term1 = generate_bool_term(ctx, depth + 1)
        term2 = generate_bool_term(ctx, depth + 1)
        return f"(xor {term1} {term2})"
    
    elif production == 'implies':
        num_terms = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(num_terms)]
        return f"(=> {' '.join(terms)})"
    
    elif production == 'bool_eq':
        term1 = generate_bool_term(ctx, depth + 1)
        term2 = generate_bool_term(ctx, depth + 1)
        return f"(= {term1} {term2})"
    
    elif production == 'bool_distinct':
        num_terms = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(num_terms)]
        return f"(distinct {' '.join(terms)})"
    
    else:  # ite
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_bool_term(ctx, depth + 1)
        else_branch = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"

# ============================================================================
# Main generation function
# ============================================================================
def generate_z3characters_formula_with_decls():
    """Generate a random z3_characters formula with declarations."""
    ctx = initialize_context()
    formula = generate_bool_term(ctx, 0)
    decls = ctx.get_declarations()
    return decls, formula