import random

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'let', 'true', 'false', 'exists', 'forall',
    'assert', 'check-sat', 'declare-fun', 'declare-const', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'distinct', 'mod', 'div', 'abs', 'str', 're', 'int', 'bool', 'string',
    'reglan', 'as', 'par', 'match', 'case'
}

# ============================================================================
# Random Name Generation
# ============================================================================
def generate_random_name(min_length=5):
    """Generate a random name with only lowercase letters, avoiding keywords."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and depth
# ============================================================================
class GeneratorContext:
    def __init__(self, max_depth=5):
        self.max_depth = max_depth
        self.bool_vars = []
        self.string_vars = []
        self.int_vars = []
        self.regex_vars = []
        self.let_bound_vars = {}  # name -> sort
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
        
    def add_string_var(self, name):
        self.string_vars.append(name)
        
    def add_int_var(self, name):
        self.int_vars.append(name)
        
    def add_regex_var(self, name):
        self.regex_vars.append(name)
        
    def get_declarations(self):
        decls = []
        for v in self.bool_vars:
            decls.append(f"(declare-const {v} Bool)")
        for v in self.string_vars:
            decls.append(f"(declare-const {v} String)")
        for v in self.int_vars:
            decls.append(f"(declare-const {v} Int)")
        for v in self.regex_vars:
            decls.append(f"(declare-const {v} RegLan)")
        return '\n'.join(decls)

# ============================================================================
# String Literal Generation
# ============================================================================
def generate_string_literal():
    """Generate a random string literal."""
    length = random.randint(0, 5)
    chars = []
    for _ in range(length):
        # Use simple printable ASCII characters
        chars.append(random.choice('abcdefghijklmnopqrstuvwxyz0123456789 '))
    return f'"{" ".join(chars)}"'

# ============================================================================
# Integer Literal Generation
# ============================================================================
def generate_integer_literal():
    """Generate a random integer literal."""
    val = random.randint(-10, 20)
    if val < 0:
        return f"(- {-val})"
    return str(val)

# ============================================================================
# Term Generation Functions
# ============================================================================
def generate_bool_term(ctx, depth=0):
    """Generate a random Boolean term."""
    if depth >= ctx.max_depth:
        # Base case: return simple term
        choices = ['true', 'false']
        if ctx.bool_vars:
            choices.append('var')
        choice = random.choice(choices)
        if choice == 'var':
            return random.choice(ctx.bool_vars)
        return choice
    
    # Choose production
    productions = [
        'true', 'false', 'var', 'string_comparison', 'int_comparison',
        'regex_membership', 'bool_operation', 'ite'
    ]
    
    # Weight towards more interesting productions
    weights = [1, 1, 3, 5, 5, 3, 8, 2]
    
    if not ctx.bool_vars:
        productions.remove('var')
        weights.pop(2)
    
    production = random.choices(productions, weights=weights, k=1)[0]
    
    if production == 'true':
        return 'true'
    elif production == 'false':
        return 'false'
    elif production == 'var':
        return random.choice(ctx.bool_vars)
    elif production == 'string_comparison':
        return generate_string_comparison(ctx, depth)
    elif production == 'int_comparison':
        return generate_int_comparison(ctx, depth)
    elif production == 'regex_membership':
        return generate_regex_membership(ctx, depth)
    elif production == 'bool_operation':
        return generate_bool_operation(ctx, depth)
    elif production == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_bool_term(ctx, depth + 1)
        else_branch = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    
    return 'true'

def generate_bool_operation(ctx, depth):
    """Generate a Boolean operation."""
    ops = ['not', 'and', 'or', 'xor', '=>', '=', 'distinct']
    op = random.choice(ops)
    
    if op == 'not':
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"
    elif op == 'xor':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(xor {arg1} {arg2})"
    elif op == '=>':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(=> {arg1} {arg2})"
    elif op == '=':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(= {arg1} {arg2})"
    elif op in ['and', 'or', 'distinct']:
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    
    return 'true'

def generate_string_comparison(ctx, depth):
    """Generate a string comparison."""
    ops = ['=', 'distinct', 'str.prefixof', 'str.suffixof', 'str.<', 'str.<=', 'str.is_digit']
    op = random.choice(ops)
    
    if op == 'str.is_digit':
        arg = generate_string_term(ctx, depth + 1)
        return f"(str.is_digit {arg})"
    elif op in ['str.prefixof', 'str.suffixof', 'str.<', 'str.<=', '=']:
        arg1 = generate_string_term(ctx, depth + 1)
        arg2 = generate_string_term(ctx, depth + 1)
        return f"({op} {arg1} {arg2})"
    elif op == 'distinct':
        num_args = random.randint(2, 3)
        args = [generate_string_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(distinct {' '.join(args)})"
    
    return 'true'

def generate_int_comparison(ctx, depth):
    """Generate an integer comparison."""
    ops = ['=', '<', '<=', '>', '>=', 'distinct']
    op = random.choice(ops)
    
    if op == 'distinct':
        num_args = random.randint(2, 3)
        args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(distinct {' '.join(args)})"
    else:
        arg1 = generate_int_term(ctx, depth + 1)
        arg2 = generate_int_term(ctx, depth + 1)
        return f"({op} {arg1} {arg2})"

def generate_regex_membership(ctx, depth):
    """Generate a regex membership test."""
    str_arg = generate_string_term(ctx, depth + 1)
    regex_arg = generate_regex_term(ctx, depth + 1)
    return f"(str.in_re {str_arg} {regex_arg})"

def generate_string_term(ctx, depth):
    """Generate a string term."""
    if depth >= ctx.max_depth:
        choices = ['literal']
        if ctx.string_vars:
            choices.append('var')
        choice = random.choice(choices)
        if choice == 'var':
            return random.choice(ctx.string_vars)
        return generate_string_literal()
    
    productions = [
        'literal', 'var', 'str.++', 'str.substr', 'str.at', 'str.replace',
        'str.replace_all', 'str.replace_re', 'str.replace_re_all', 'str.update',
        'str.rev', 'str.to_lower', 'str.to_upper', 'str.from_code', 'str.from_int',
        'ite'
    ]
    
    weights = [3, 5, 4, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1]
    
    if not ctx.string_vars:
        productions.remove('var')
        weights.pop(1)
    
    production = random.choices(productions, weights=weights, k=1)[0]
    
    if production == 'literal':
        return generate_string_literal()
    elif production == 'var':
        return random.choice(ctx.string_vars)
    elif production == 'str.++':
        num_args = random.randint(2, 3)
        args = [generate_string_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(str.++ {' '.join(args)})"
    elif production == 'str.substr':
        s = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        n = generate_int_term(ctx, depth + 1)
        return f"(str.substr {s} {i} {n})"
    elif production == 'str.at':
        s = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(str.at {s} {i})"
    elif production == 'str.replace':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        s3 = generate_string_term(ctx, depth + 1)
        return f"(str.replace {s1} {s2} {s3})"
    elif production == 'str.replace_all':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        s3 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_all {s1} {s2} {s3})"
    elif production == 'str.replace_re':
        s1 = generate_string_term(ctx, depth + 1)
        r = generate_regex_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_re {s1} {r} {s2})"
    elif production == 'str.replace_re_all':
        s1 = generate_string_term(ctx, depth + 1)
        r = generate_regex_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_re_all {s1} {r} {s2})"
    elif production == 'str.update':
        s1 = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(str.update {s1} {i} {s2})"
    elif production == 'str.rev':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.rev {s})"
    elif production == 'str.to_lower':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_lower {s})"
    elif production == 'str.to_upper':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_upper {s})"
    elif production == 'str.from_code':
        i = generate_int_term(ctx, depth + 1)
        return f"(str.from_code {i})"
    elif production == 'str.from_int':
        i = generate_int_term(ctx, depth + 1)
        return f"(str.from_int {i})"
    elif production == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_string_term(ctx, depth + 1)
        else_branch = generate_string_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    
    return generate_string_literal()

def generate_int_term(ctx, depth):
    """Generate an integer term."""
    if depth >= ctx.max_depth:
        choices = ['literal']
        if ctx.int_vars:
            choices.append('var')
        choice = random.choice(choices)
        if choice == 'var':
            return random.choice(ctx.int_vars)
        return generate_integer_literal()
    
    productions = [
        'literal', 'var', 'str.len', 'str.to_code', 'str.to_int', 'str.indexof',
        'str.indexof_re', '+', '-', '*', 'div', 'mod', 'abs', 'ite'
    ]
    
    weights = [3, 5, 3, 2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 1]
    
    if not ctx.int_vars:
        productions.remove('var')
        weights.pop(1)
    
    production = random.choices(productions, weights=weights, k=1)[0]
    
    if production == 'literal':
        return generate_integer_literal()
    elif production == 'var':
        return random.choice(ctx.int_vars)
    elif production == 'str.len':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.len {s})"
    elif production == 'str.to_code':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_code {s})"
    elif production == 'str.to_int':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_int {s})"
    elif production == 'str.indexof':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(str.indexof {s1} {s2} {i})"
    elif production == 'str.indexof_re':
        s = generate_string_term(ctx, depth + 1)
        r = generate_regex_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(str.indexof_re {s} {r} {i})"
    elif production == '+':
        num_args = random.randint(2, 3)
        args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(+ {' '.join(args)})"
    elif production == '-':
        if random.random() < 0.3:
            arg = generate_int_term(ctx, depth + 1)
            return f"(- {arg})"
        else:
            arg1 = generate_int_term(ctx, depth + 1)
            arg2 = generate_int_term(ctx, depth + 1)
            return f"(- {arg1} {arg2})"
    elif production == '*':
        num_args = random.randint(2, 3)
        args = [generate_int_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(* {' '.join(args)})"
    elif production == 'div':
        arg1 = generate_int_term(ctx, depth + 1)
        arg2 = generate_int_term(ctx, depth + 1)
        return f"(div {arg1} {arg2})"
    elif production == 'mod':
        arg1 = generate_int_term(ctx, depth + 1)
        arg2 = generate_int_term(ctx, depth + 1)
        return f"(mod {arg1} {arg2})"
    elif production == 'abs':
        arg = generate_int_term(ctx, depth + 1)
        return f"(abs {arg})"
    elif production == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_int_term(ctx, depth + 1)
        else_branch = generate_int_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    
    return generate_integer_literal()

def generate_regex_term(ctx, depth):
    """Generate a regex term."""
    if depth >= ctx.max_depth:
        choices = ['str.to_re']
        if ctx.regex_vars:
            choices.append('var')
        choice = random.choice(choices)
        if choice == 'var':
            return random.choice(ctx.regex_vars)
        else:
            s = generate_string_literal()
            return f"(str.to_re {s})"
    
    productions = [
        'var', 'str.to_re', 're.none', 're.all', 're.allchar', 're.++', 're.union',
        're.inter', 're.*', 're.+', 're.opt', 're.range', 're.^', 're.loop',
        're.comp', 're.diff', 'ite'
    ]
    
    weights = [3, 4, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1]
    
    if not ctx.regex_vars:
        productions.remove('var')
        weights.pop(0)
    
    production = random.choices(productions, weights=weights, k=1)[0]
    
    if production == 'var':
        return random.choice(ctx.regex_vars)
    elif production == 'str.to_re':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_re {s})"
    elif production == 're.none':
        return 're.none'
    elif production == 're.all':
        return 're.all'
    elif production == 're.allchar':
        return 're.allchar'
    elif production == 're.++':
        num_args = random.randint(2, 3)
        args = [generate_regex_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(re.++ {' '.join(args)})"
    elif production == 're.union':
        num_args = random.randint(2, 3)
        args = [generate_regex_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(re.union {' '.join(args)})"
    elif production == 're.inter':
        num_args = random.randint(2, 3)
        args = [generate_regex_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(re.inter {' '.join(args)})"
    elif production == 're.*':
        r = generate_regex_term(ctx, depth + 1)
        return f"(re.* {r})"
    elif production == 're.+':
        r = generate_regex_term(ctx, depth + 1)
        return f"(re.+ {r})"
    elif production == 're.opt':
        r = generate_regex_term(ctx, depth + 1)
        return f"(re.opt {r})"
    elif production == 're.range':
        s1 = generate_string_literal()
        s2 = generate_string_literal()
        return f"(re.range {s1} {s2})"
    elif production == 're.^':
        r = generate_regex_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(re.^ {r} {i})"
    elif production == 're.loop':
        i1 = generate_int_term(ctx, depth + 1)
        i2 = generate_int_term(ctx, depth + 1)
        r = generate_regex_term(ctx, depth + 1)
        return f"(re.loop {i1} {i2} {r})"
    elif production == 're.comp':
        r = generate_regex_term(ctx, depth + 1)
        return f"(re.comp {r})"
    elif production == 're.diff':
        r1 = generate_regex_term(ctx, depth + 1)
        r2 = generate_regex_term(ctx, depth + 1)
        return f"(re.diff {r1} {r2})"
    elif production == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_regex_term(ctx, depth + 1)
        else_branch = generate_regex_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    
    s = generate_string_literal()
    return f"(str.to_re {s})"

# ============================================================================
# Main Generator Function
# ============================================================================
def generate_cvc5strings_formula_with_decls():
    """Generate a random cvc5_Strings formula with declarations."""
    ctx = GeneratorContext(max_depth=random.randint(3, 6))
    
    # Generate random number of variables
    num_bool_vars = random.randint(1, 4)
    num_string_vars = random.randint(1, 4)
    num_int_vars = random.randint(1, 4)
    num_regex_vars = random.randint(0, 2)
    
    for _ in range(num_bool_vars):
        ctx.add_bool_var(generate_random_name())
    
    for _ in range(num_string_vars):
        ctx.add_string_var(generate_random_name())
    
    for _ in range(num_int_vars):
        ctx.add_int_var(generate_random_name())
    
    for _ in range(num_regex_vars):
        ctx.add_regex_var(generate_random_name())
    
    # Generate the formula
    formula = generate_bool_term(ctx, depth=0)
    
    # Get declarations
    decls = ctx.get_declarations()
    
    return decls, formula