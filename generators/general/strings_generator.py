import random

# ============================================================================
# SMT-LIB Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'match', 'par', 'assert', 'check-sat', 'declare-fun', 'declare-const',
    'define-fun', 'set-logic', 'set-option', 'get-model', 'get-value',
    'push', 'pop', 'exit', 'echo', 'reset', 'Int', 'Bool', 'String', 'RegLan',
    'div', 'mod', 'abs', 'distinct', 're', 'str', 'none', 'all', 'allchar',
}

# ============================================================================
# Name generation
# ============================================================================
def generate_name(min_len=5, max_len=12):
    """Generate a random lowercase name avoiding SMT-LIB keywords."""
    while True:
        length = random.randint(min_len, max_len)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Global context for declarations
# ============================================================================
class Context:
    def __init__(self):
        self.bool_vars = []
        self.string_vars = []
        self.int_vars = []
        self.reglan_vars = []
        self.depth_limit = 6
        
    def add_bool_var(self):
        name = generate_name()
        self.bool_vars.append(name)
        return name
    
    def add_string_var(self):
        name = generate_name()
        self.string_vars.append(name)
        return name
    
    def add_int_var(self):
        name = generate_name()
        self.int_vars.append(name)
        return name
    
    def add_reglan_var(self):
        name = generate_name()
        self.reglan_vars.append(name)
        return name
    
    def get_decls(self):
        decls = []
        for v in self.bool_vars:
            decls.append(f"(declare-const {v} Bool)")
        for v in self.string_vars:
            decls.append(f"(declare-const {v} String)")
        for v in self.int_vars:
            decls.append(f"(declare-const {v} Int)")
        for v in self.reglan_vars:
            decls.append(f"(declare-const {v} RegLan)")
        return '\n'.join(decls)

# ============================================================================
# Literal generators
# ============================================================================
def generate_numeral():
    """Generate a non-negative integer literal."""
    return str(random.randint(0, 100))

def generate_int_literal():
    """Generate an integer literal (positive or negative)."""
    val = random.randint(-50, 100)
    if val < 0:
        return f"(- {-val})"
    return str(val)

def generate_hex_digit():
    return random.choice('0123456789abcdef')

def generate_hex_code():
    """Generate a hex code for singleton char."""
    choice = random.randint(0, 4)
    if choice == 0:
        return f"#x{generate_hex_digit()}"
    elif choice == 1:
        return f"#x{generate_hex_digit()}{generate_hex_digit()}"
    elif choice == 2:
        return f"#x{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}"
    elif choice == 3:
        return f"#x{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}"
    else:
        prefix = random.choice(['0', '1', '2'])
        return f"#x{prefix}{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}"

def generate_singleton_char():
    """Generate a singleton character constant."""
    return f"(_ char {generate_hex_code()})"

def generate_string_literal():
    """Generate a string literal with possible escape sequences."""
    length = random.randint(0, 5)
    chars = []
    for _ in range(length):
        choice = random.randint(0, 10)
        if choice < 7:
            # Printable ASCII (excluding " and \)
            c = random.choice('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 !#$%&\'()*+,-./:;<=>?@[]^_`{|}~')
            chars.append(c)
        elif choice < 9:
            # Double quote escape
            chars.append('""')
        else:
            # Unicode escape
            esc_choice = random.randint(0, 4)
            if esc_choice == 0:
                chars.append(f"\\u{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}")
            elif esc_choice == 1:
                chars.append(f"\\u{{{generate_hex_digit()}}}")
            elif esc_choice == 2:
                chars.append(f"\\u{{{generate_hex_digit()}{generate_hex_digit()}}}")
            elif esc_choice == 3:
                chars.append(f"\\u{{{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}}}")
            else:
                chars.append(f"\\u{{{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}{generate_hex_digit()}}}")
    return f'"{" ".join(chars)}"'

# ============================================================================
# Term generators
# ============================================================================
def generate_string_term(ctx, depth):
    """Generate a string term."""
    if depth >= ctx.depth_limit:
        # Base case
        choice = random.randint(0, 2)
        if choice == 0:
            return generate_string_literal()
        elif choice == 1 and ctx.string_vars:
            return random.choice(ctx.string_vars)
        else:
            return generate_singleton_char()
    
    choices = [
        'literal', 'var', 'singleton', 'concat', 'at', 'substr',
        'replace', 'replace_all', 'replace_re', 'replace_re_all',
        'from_code', 'from_int', 'ite'
    ]
    
    choice = random.choice(choices)
    
    if choice == 'literal':
        return generate_string_literal()
    elif choice == 'var':
        if ctx.string_vars and random.random() < 0.7:
            return random.choice(ctx.string_vars)
        return generate_string_literal()
    elif choice == 'singleton':
        return generate_singleton_char()
    elif choice == 'concat':
        n = random.randint(2, 3)
        terms = [generate_string_term(ctx, depth + 1) for _ in range(n)]
        return f"(str.++ {' '.join(terms)})"
    elif choice == 'at':
        s = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(str.at {s} {i})"
    elif choice == 'substr':
        s = generate_string_term(ctx, depth + 1)
        i1 = generate_int_term(ctx, depth + 1)
        i2 = generate_int_term(ctx, depth + 1)
        return f"(str.substr {s} {i1} {i2})"
    elif choice == 'replace':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        s3 = generate_string_term(ctx, depth + 1)
        return f"(str.replace {s1} {s2} {s3})"
    elif choice == 'replace_all':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        s3 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_all {s1} {s2} {s3})"
    elif choice == 'replace_re':
        s1 = generate_string_term(ctx, depth + 1)
        r = generate_reglan_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_re {s1} {r} {s2})"
    elif choice == 'replace_re_all':
        s1 = generate_string_term(ctx, depth + 1)
        r = generate_reglan_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(str.replace_re_all {s1} {r} {s2})"
    elif choice == 'from_code':
        i = generate_int_term(ctx, depth + 1)
        return f"(str.from_code {i})"
    elif choice == 'from_int':
        i = generate_int_term(ctx, depth + 1)
        return f"(str.from_int {i})"
    else:  # ite
        b = generate_bool_term(ctx, depth + 1)
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(ite {b} {s1} {s2})"

def generate_int_term(ctx, depth):
    """Generate an integer term."""
    if depth >= ctx.depth_limit:
        # Base case
        if ctx.int_vars and random.random() < 0.5:
            return random.choice(ctx.int_vars)
        return generate_int_literal()
    
    choices = [
        'literal', 'var', 'arith', 'neg', 'len', 'indexof',
        'to_code', 'to_int', 'ite'
    ]
    
    choice = random.choice(choices)
    
    if choice == 'literal':
        return generate_int_literal()
    elif choice == 'var':
        if ctx.int_vars and random.random() < 0.7:
            return random.choice(ctx.int_vars)
        return generate_int_literal()
    elif choice == 'arith':
        op = random.choice(['+', '*', '-', 'div', 'mod', 'abs'])
        if op == 'abs':
            i = generate_int_term(ctx, depth + 1)
            return f"(abs {i})"
        elif op in ['div', 'mod']:
            # div and mod require exactly 2 arguments
            i1 = generate_int_term(ctx, depth + 1)
            i2 = generate_int_term(ctx, depth + 1)
            return f"({op} {i1} {i2})"
        else:
            # +, *, - can have 2 or more arguments
            n = random.randint(2, 3)
            terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
            return f"({op} {' '.join(terms)})"
    elif choice == 'neg':
        i = generate_int_term(ctx, depth + 1)
        return f"(- {i})"
    elif choice == 'len':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.len {s})"
    elif choice == 'indexof':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        i = generate_int_term(ctx, depth + 1)
        return f"(str.indexof {s1} {s2} {i})"
    elif choice == 'to_code':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_code {s})"
    elif choice == 'to_int':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_int {s})"
    else:  # ite
        b = generate_bool_term(ctx, depth + 1)
        i1 = generate_int_term(ctx, depth + 1)
        i2 = generate_int_term(ctx, depth + 1)
        return f"(ite {b} {i1} {i2})"

def generate_reglan_term(ctx, depth):
    """Generate a regular expression term."""
    if depth >= ctx.depth_limit:
        # Base case
        choices = ['none', 'all', 'allchar', 'var', 'to_re']
        choice = random.choice(choices)
        if choice == 'none':
            return 're.none'
        elif choice == 'all':
            return 're.all'
        elif choice == 'allchar':
            return 're.allchar'
        elif choice == 'var' and ctx.reglan_vars:
            return random.choice(ctx.reglan_vars)
        else:
            s = generate_string_term(ctx, depth + 1)
            return f"(str.to_re {s})"
    
    choices = [
        'none', 'all', 'allchar', 'var', 'to_re', 'concat', 'union',
        'inter', 'star', 'plus', 'opt', 'comp', 'diff', 'range',
        'power', 'loop', 'ite'
    ]
    
    choice = random.choice(choices)
    
    if choice == 'none':
        return 're.none'
    elif choice == 'all':
        return 're.all'
    elif choice == 'allchar':
        return 're.allchar'
    elif choice == 'var':
        if ctx.reglan_vars and random.random() < 0.5:
            return random.choice(ctx.reglan_vars)
        return 're.allchar'
    elif choice == 'to_re':
        s = generate_string_term(ctx, depth + 1)
        return f"(str.to_re {s})"
    elif choice == 'concat':
        n = random.randint(2, 3)
        terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(re.++ {' '.join(terms)})"
    elif choice == 'union':
        n = random.randint(2, 3)
        terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(re.union {' '.join(terms)})"
    elif choice == 'inter':
        n = random.randint(2, 3)
        terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(re.inter {' '.join(terms)})"
    elif choice == 'star':
        r = generate_reglan_term(ctx, depth + 1)
        return f"(re.* {r})"
    elif choice == 'plus':
        r = generate_reglan_term(ctx, depth + 1)
        return f"(re.+ {r})"
    elif choice == 'opt':
        r = generate_reglan_term(ctx, depth + 1)
        return f"(re.opt {r})"
    elif choice == 'comp':
        r = generate_reglan_term(ctx, depth + 1)
        return f"(re.comp {r})"
    elif choice == 'diff':
        n = random.randint(2, 3)
        terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(re.diff {' '.join(terms)})"
    elif choice == 'range':
        s1 = generate_string_term(ctx, depth + 1)
        s2 = generate_string_term(ctx, depth + 1)
        return f"(re.range {s1} {s2})"
    elif choice == 'power':
        n = generate_numeral()
        r = generate_reglan_term(ctx, depth + 1)
        return f"((_ re.^ {n}) {r})"
    elif choice == 'loop':
        n1 = generate_numeral()
        n2 = generate_numeral()
        r = generate_reglan_term(ctx, depth + 1)
        return f"((_ re.loop {n1} {n2}) {r})"
    else:  # ite
        b = generate_bool_term(ctx, depth + 1)
        r1 = generate_reglan_term(ctx, depth + 1)
        r2 = generate_reglan_term(ctx, depth + 1)
        return f"(ite {b} {r1} {r2})"

def generate_term(ctx, depth):
    """Generate a generic term (any sort)."""
    sort = random.choice(['bool', 'string', 'int', 'reglan'])
    if sort == 'bool':
        return generate_bool_term(ctx, depth)
    elif sort == 'string':
        return generate_string_term(ctx, depth)
    elif sort == 'int':
        return generate_int_term(ctx, depth)
    else:
        return generate_reglan_term(ctx, depth)

def generate_bool_term(ctx, depth):
    """Generate a Boolean term."""
    if depth >= ctx.depth_limit:
        # Base case
        choices = ['true', 'false', 'var']
        choice = random.choice(choices)
        if choice == 'true':
            return 'true'
        elif choice == 'false':
            return 'false'
        else:
            if ctx.bool_vars and random.random() < 0.7:
                return random.choice(ctx.bool_vars)
            return random.choice(['true', 'false'])
    
    choices = [
        'true', 'false', 'var', 'bool_op', 'not', 'implies',
        'eq', 'distinct', 'ite', 'string_pred', 're_pred', 'int_comp'
    ]
    
    choice = random.choice(choices)
    
    if choice == 'true':
        return 'true'
    elif choice == 'false':
        return 'false'
    elif choice == 'var':
        if ctx.bool_vars and random.random() < 0.5:
            return random.choice(ctx.bool_vars)
        return random.choice(['true', 'false'])
    elif choice == 'bool_op':
        op = random.choice(['and', 'or', 'xor'])
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"({op} {' '.join(terms)})"
    elif choice == 'not':
        b = generate_bool_term(ctx, depth + 1)
        return f"(not {b})"
    elif choice == 'implies':
        n = random.randint(2, 3)
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(=> {' '.join(terms)})"
    elif choice == 'eq':
        n = random.randint(2, 3)
        # Pick a sort and generate terms of that sort
        sort = random.choice(['bool', 'string', 'int', 'reglan'])
        if sort == 'bool':
            terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        elif sort == 'string':
            terms = [generate_string_term(ctx, depth + 1) for _ in range(n)]
        elif sort == 'int':
            terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        else:
            terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(= {' '.join(terms)})"
    elif choice == 'distinct':
        n = random.randint(2, 3)
        sort = random.choice(['bool', 'string', 'int', 'reglan'])
        if sort == 'bool':
            terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        elif sort == 'string':
            terms = [generate_string_term(ctx, depth + 1) for _ in range(n)]
        elif sort == 'int':
            terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        else:
            terms = [generate_reglan_term(ctx, depth + 1) for _ in range(n)]
        return f"(distinct {' '.join(terms)})"
    elif choice == 'ite':
        b = generate_bool_term(ctx, depth + 1)
        # ite returns a term, but we need a bool term here
        t1 = generate_bool_term(ctx, depth + 1)
        t2 = generate_bool_term(ctx, depth + 1)
        return f"(ite {b} {t1} {t2})"
    elif choice == 'string_pred':
        pred_choice = random.choice(['lt', 'le', 'prefixof', 'suffixof', 'contains', 'is_digit'])
        if pred_choice == 'lt':
            # str.< requires exactly 2 arguments
            s1 = generate_string_term(ctx, depth + 1)
            s2 = generate_string_term(ctx, depth + 1)
            return f"(str.< {s1} {s2})"
        elif pred_choice == 'le':
            # str.<= requires exactly 2 arguments
            s1 = generate_string_term(ctx, depth + 1)
            s2 = generate_string_term(ctx, depth + 1)
            return f"(str.<= {s1} {s2})"
        elif pred_choice == 'prefixof':
            s1 = generate_string_term(ctx, depth + 1)
            s2 = generate_string_term(ctx, depth + 1)
            return f"(str.prefixof {s1} {s2})"
        elif pred_choice == 'suffixof':
            s1 = generate_string_term(ctx, depth + 1)
            s2 = generate_string_term(ctx, depth + 1)
            return f"(str.suffixof {s1} {s2})"
        elif pred_choice == 'contains':
            s1 = generate_string_term(ctx, depth + 1)
            s2 = generate_string_term(ctx, depth + 1)
            return f"(str.contains {s1} {s2})"
        else:  # is_digit
            s = generate_string_term(ctx, depth + 1)
            return f"(str.is_digit {s})"
    elif choice == 're_pred':
        s = generate_string_term(ctx, depth + 1)
        r = generate_reglan_term(ctx, depth + 1)
        return f"(str.in_re {s} {r})"
    else:  # int_comp
        op = random.choice(['<', '<=', '>', '>='])
        n = random.randint(2, 3)
        terms = [generate_int_term(ctx, depth + 1) for _ in range(n)]
        return f"({op} {' '.join(terms)})"

# ============================================================================
# Main generator
# ============================================================================
def generate_strings_formula_with_decls():
    """Generate a random Strings theory formula with declarations."""
    ctx = Context()
    
    # Create a random number of variables
    num_bool_vars = random.randint(1, 4)
    num_string_vars = random.randint(1, 4)
    num_int_vars = random.randint(1, 4)
    num_reglan_vars = random.randint(0, 2)
    
    for _ in range(num_bool_vars):
        ctx.add_bool_var()
    for _ in range(num_string_vars):
        ctx.add_string_var()
    for _ in range(num_int_vars):
        ctx.add_int_var()
    for _ in range(num_reglan_vars):
        ctx.add_reglan_var()
    
    # Generate the formula
    formula = generate_bool_term(ctx, 0)
    
    # Get declarations
    decls = ctx.get_decls()
    
    return decls, formula