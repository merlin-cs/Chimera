import random
import string

# ============================================================
# SMT-LIB Keyword Blacklist
# ============================================================
SMTLIB_KEYWORDS = {
    'true', 'false', 'not', 'and', 'or', 'xor', 'ite', 'let', 'forall', 'exists',
    'as', 'distinct', 'bag', 'member', 'subbag', 'count', 'union', 'inter',
    'difference', 'setof', 'empty', 'Bool', 'Int', 'String', 'Real', 'Bag',
    'abs', 'div', 'mod', 'str', 'substr', 'to', 'disjoint', 'max', 'min',
    'subtract', 'remove', 'assert', 'check', 'sat', 'declare', 'define',
    'fun', 'const', 'sort', 'logic', 'set', 'get', 'push', 'pop', 'exit'
}

# ============================================================
# Name Generation
# ============================================================
def generate_name(prefix='', min_len=5):
    while True:
        length = random.randint(min_len, min_len + 5)
        name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS and len(name) >= min_len:
            return name

# ============================================================
# Context for tracking declarations and depth
# ============================================================
class Context:
    def __init__(self):
        self.bag_vars = []
        self.int_vars = []
        self.bool_vars = []
        self.string_vars = []
        self.element_vars = []
        self.element_funcs = []
        self.bag_element_sort = 'Int'
        self.max_depth = 6
        self.decls = []
        
    def add_bag_var(self, name):
        self.bag_vars.append(name)
        self.decls.append(f"(declare-const {name} (Bag {self.bag_element_sort}))")
        
    def add_int_var(self, name):
        self.int_vars.append(name)
        self.decls.append(f"(declare-const {name} Int)")
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
        self.decls.append(f"(declare-const {name} Bool)")
        
    def add_string_var(self, name):
        self.string_vars.append(name)
        self.decls.append(f"(declare-const {name} String)")
        
    def add_element_var(self, name):
        self.element_vars.append(name)
        self.decls.append(f"(declare-const {name} {self.bag_element_sort})")
        
    def add_element_func(self, name, arity):
        self.element_funcs.append((name, arity))
        args = ' '.join([self.bag_element_sort] * arity)
        self.decls.append(f"(declare-fun {name} ({args}) {self.bag_element_sort})")

# ============================================================
# Term Generators
# ============================================================

def generate_bool_term(ctx, depth=0):
    if depth >= ctx.max_depth:
        return generate_bool_leaf(ctx)
    
    choices = [
        ('leaf', 3),
        ('predicate', 5),
        ('connective', 4),
        ('quantifier', 1),
        ('ite', 2)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'leaf':
        return generate_bool_leaf(ctx)
    elif choice == 'predicate':
        return generate_bag_predicate(ctx, depth)
    elif choice == 'connective':
        return generate_bool_connective(ctx, depth)
    elif choice == 'quantifier':
        return generate_quantifier(ctx, depth)
    else:
        return generate_bool_ite(ctx, depth)

def generate_bool_leaf(ctx):
    choices = ['const', 'var']
    if ctx.bool_vars:
        choice = random.choice(choices)
    else:
        choice = 'const'
    
    if choice == 'const':
        return random.choice(['true', 'false'])
    else:
        return random.choice(ctx.bool_vars)

def generate_bag_predicate(ctx, depth):
    pred_type = random.choice(['member', 'subbag', 'equality', 'count_cmp'])
    
    if pred_type == 'member':
        elem = generate_element_term(ctx, depth + 1)
        bag = generate_bag_term(ctx, depth + 1)
        return f"(bag.member {elem} {bag})"
    elif pred_type == 'subbag':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.subbag {bag1} {bag2})"
    elif pred_type == 'equality':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(= {bag1} {bag2})"
    else:
        op = random.choice(['=', '<', '<=', '>', '>='])
        elem = generate_element_term(ctx, depth + 1)
        bag = generate_bag_term(ctx, depth + 1)
        count = f"(bag.count {elem} {bag})"
        int_term = generate_int_term(ctx, depth + 1)
        if random.choice([True, False]):
            return f"({op} {count} {int_term})"
        else:
            return f"({op} {int_term} {count})"

def generate_bool_connective(ctx, depth):
    conn_type = random.choice(['not', 'and', 'or', '=>', 'xor', '=', 'distinct'])
    
    if conn_type == 'not':
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"
    elif conn_type in ['and', 'or']:
        n = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"({conn_type} {' '.join(args)})"
    elif conn_type in ['=>', 'xor']:
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"({conn_type} {arg1} {arg2})"
    elif conn_type == '=':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(= {arg1} {arg2})"
    else:
        n = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f"(distinct {' '.join(args)})"

def generate_bool_ite(ctx, depth):
    cond = generate_bool_term(ctx, depth + 1)
    then_branch = generate_bool_term(ctx, depth + 1)
    else_branch = generate_bool_term(ctx, depth + 1)
    return f"(ite {cond} {then_branch} {else_branch})"

def generate_quantifier(ctx, depth):
    quant = random.choice(['forall', 'exists'])
    n_vars = random.randint(1, 2)
    sorted_vars = []
    var_names = []
    
    for _ in range(n_vars):
        var_name = generate_name('qvar')
        var_names.append(var_name)
        sort = random.choice(['Int', 'Bool', ctx.bag_element_sort])
        sorted_vars.append(f"({var_name} {sort})")
    
    body = generate_bool_term(ctx, depth + 1)
    return f"({quant} ({' '.join(sorted_vars)}) {body})"

def generate_bag_term(ctx, depth):
    if depth >= ctx.max_depth or not ctx.bag_vars:
        return generate_bag_leaf(ctx)
    
    choices = [
        ('leaf', 4),
        ('singleton', 3),
        ('union_disjoint', 2),
        ('union_max', 2),
        ('inter_min', 2),
        ('diff_subtract', 2),
        ('diff_remove', 2),
        ('setof', 1),
        ('ite', 1)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'leaf':
        return generate_bag_leaf(ctx)
    elif choice == 'singleton':
        elem = generate_element_term(ctx, depth + 1)
        mult = generate_int_term(ctx, depth + 1)
        return f"(bag {elem} {mult})"
    elif choice == 'union_disjoint':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.union_disjoint {bag1} {bag2})"
    elif choice == 'union_max':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.union_max {bag1} {bag2})"
    elif choice == 'inter_min':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.inter_min {bag1} {bag2})"
    elif choice == 'diff_subtract':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.difference_subtract {bag1} {bag2})"
    elif choice == 'diff_remove':
        bag1 = generate_bag_term(ctx, depth + 1)
        bag2 = generate_bag_term(ctx, depth + 1)
        return f"(bag.difference_remove {bag1} {bag2})"
    elif choice == 'setof':
        bag = generate_bag_term(ctx, depth + 1)
        return f"(bag.setof {bag})"
    else:
        cond = generate_bool_term(ctx, depth + 1)
        then_bag = generate_bag_term(ctx, depth + 1)
        else_bag = generate_bag_term(ctx, depth + 1)
        return f"(ite {cond} {then_bag} {else_bag})"

def generate_bag_leaf(ctx):
    if ctx.bag_vars and random.random() < 0.7:
        return random.choice(ctx.bag_vars)
    else:
        return f"(as bag.empty (Bag {ctx.bag_element_sort}))"

def generate_element_term(ctx, depth):
    if ctx.bag_element_sort == 'Int':
        return generate_int_term(ctx, depth)
    elif ctx.bag_element_sort == 'String':
        return generate_string_term(ctx, depth)
    elif ctx.bag_element_sort == 'Bool':
        return generate_bool_term(ctx, depth)
    else:
        if ctx.element_vars and random.random() < 0.6:
            return random.choice(ctx.element_vars)
        elif ctx.element_funcs and random.random() < 0.3:
            func, arity = random.choice(ctx.element_funcs)
            args = [generate_element_term(ctx, depth + 1) for _ in range(arity)]
            return f"({func} {' '.join(args)})"
        else:
            if ctx.element_vars:
                return random.choice(ctx.element_vars)
            else:
                return generate_int_term(ctx, depth)

def generate_int_term(ctx, depth):
    if depth >= ctx.max_depth:
        return generate_int_leaf(ctx)
    
    choices = [
        ('leaf', 5),
        ('arithmetic', 3),
        ('count', 2),
        ('ite', 1)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'leaf':
        return generate_int_leaf(ctx)
    elif choice == 'arithmetic':
        return generate_int_arithmetic(ctx, depth)
    elif choice == 'count':
        elem = generate_element_term(ctx, depth + 1)
        bag = generate_bag_term(ctx, depth + 1)
        return f"(bag.count {elem} {bag})"
    else:
        cond = generate_bool_term(ctx, depth + 1)
        then_int = generate_int_term(ctx, depth + 1)
        else_int = generate_int_term(ctx, depth + 1)
        return f"(ite {cond} {then_int} {else_int})"

def generate_int_leaf(ctx):
    if ctx.int_vars and random.random() < 0.5:
        return random.choice(ctx.int_vars)
    else:
        val = random.randint(0, 20)
        return str(val)

def generate_int_arithmetic(ctx, depth):
    op_type = random.choice(['binary', 'unary'])
    
    if op_type == 'binary':
        op = random.choice(['+', '-', '*', 'div', 'mod'])
        if op in ['+', '-', '*']:
            n = random.randint(2, 3)
            args = [generate_int_term(ctx, depth + 1) for _ in range(n)]
            return f"({op} {' '.join(args)})"
        else:
            arg1 = generate_int_term(ctx, depth + 1)
            arg2 = generate_int_term(ctx, depth + 1)
            return f"({op} {arg1} {arg2})"
    else:
        op = random.choice(['-', 'abs'])
        arg = generate_int_term(ctx, depth + 1)
        return f"({op} {arg})"

def generate_string_term(ctx, depth):
    if depth >= ctx.max_depth:
        return generate_string_leaf(ctx)
    
    choices = [
        ('leaf', 5),
        ('concat', 2),
        ('ite', 1)
    ]
    
    choice = random.choices([c[0] for c in choices], weights=[c[1] for c in choices])[0]
    
    if choice == 'leaf':
        return generate_string_leaf(ctx)
    elif choice == 'concat':
        n = random.randint(2, 3)
        args = [generate_string_term(ctx, depth + 1) for _ in range(n)]
        return f"(str.++ {' '.join(args)})"
    else:
        cond = generate_bool_term(ctx, depth + 1)
        then_str = generate_string_term(ctx, depth + 1)
        else_str = generate_string_term(ctx, depth + 1)
        return f"(ite {cond} {then_str} {else_str})"

def generate_string_leaf(ctx):
    if ctx.string_vars and random.random() < 0.5:
        return random.choice(ctx.string_vars)
    else:
        length = random.randint(0, 8)
        chars = ''.join(random.choices(string.ascii_lowercase, k=length))
        return f'"{chars}"'

# ============================================================
# Main Generator
# ============================================================

def generate_bags_formula_with_decls():
    ctx = Context()
    
    # Choose element sort for bags
    ctx.bag_element_sort = random.choice(['Int', 'String', 'Bool'])
    
    # Generate variables
    n_bag_vars = random.randint(2, 5)
    for _ in range(n_bag_vars):
        ctx.add_bag_var(generate_name('bagvar'))
    
    n_int_vars = random.randint(1, 4)
    for _ in range(n_int_vars):
        ctx.add_int_var(generate_name('intvar'))
    
    n_bool_vars = random.randint(1, 3)
    for _ in range(n_bool_vars):
        ctx.add_bool_var(generate_name('boolvar'))
    
    if ctx.bag_element_sort == 'String':
        n_string_vars = random.randint(1, 3)
        for _ in range(n_string_vars):
            ctx.add_string_var(generate_name('strvar'))
    
    # Generate element variables
    n_elem_vars = random.randint(2, 4)
    for _ in range(n_elem_vars):
        ctx.add_element_var(generate_name('elemvar'))
    
    # Generate element functions
    if random.random() < 0.4:
        n_funcs = random.randint(1, 2)
        for _ in range(n_funcs):
            arity = random.randint(1, 2)
            ctx.add_element_func(generate_name('elemfunc'), arity)
    
    # Set depth limit
    ctx.max_depth = random.randint(4, 7)
    
    # Generate formula
    formula = generate_bool_term(ctx, 0)
    
    decls_str = '\n'.join(ctx.decls)
    
    return decls_str, formula