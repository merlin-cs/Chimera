import random
import string

# SMT-LIB keywords to avoid
SMTLIB_KEYWORDS = {
    'true', 'false', 'not', 'and', 'or', 'xor', 'ite', 'distinct',
    'let', 'forall', 'exists', 'match', 'assert', 'declare-fun',
    'declare-const', 'declare-sort', 'define-fun', 'define-sort',
    'set-logic', 'set-option', 'check-sat', 'get-model', 'get-value',
    'push', 'pop', 'as', 'Bool', 'Int', 'Real', 'Array', 'BitVec',
    'par', 'lambda'
}

MAX_DEPTH = 6
MAX_CHILDREN = 4

def generate_name(prefix='', min_length=5):
    """Generate a random name with at least min_length lowercase letters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS and len(name) >= min_length:
            return name

class Context:
    def __init__(self):
        self.sorts = ['Bool']
        self.custom_sorts = []
        self.bool_vars = []
        self.typed_vars = {}
        self.typed_funcs = {}
        self.decls = []
        
    def add_custom_sort(self):
        sort_name = generate_name('sort')
        self.custom_sorts.append(sort_name)
        self.sorts.append(sort_name)
        self.decls.append(f"(declare-sort {sort_name} 0)")
        return sort_name
    
    def add_bool_var(self):
        var_name = generate_name('bvar')
        self.bool_vars.append(var_name)
        self.decls.append(f"(declare-const {var_name} Bool)")
        return var_name
    
    def add_typed_var(self, sort):
        var_name = generate_name('tvar')
        if sort not in self.typed_vars:
            self.typed_vars[sort] = []
        self.typed_vars[sort].append(var_name)
        self.decls.append(f"(declare-const {var_name} {sort})")
        return var_name
    
    def add_typed_func(self, arg_sorts, ret_sort):
        func_name = generate_name('func')
        key = (tuple(arg_sorts), ret_sort)
        if key not in self.typed_funcs:
            self.typed_funcs[key] = []
        self.typed_funcs[key].append(func_name)
        args_str = ' '.join(arg_sorts)
        self.decls.append(f"(declare-fun {func_name} ({args_str}) {ret_sort})")
        return func_name
    
    def get_vars_of_sort(self, sort):
        if sort == 'Bool':
            return self.bool_vars
        return self.typed_vars.get(sort, [])
    
    def get_funcs_of_signature(self, arg_sorts, ret_sort):
        key = (tuple(arg_sorts), ret_sort)
        return self.typed_funcs.get(key, [])

def generate_bool_constant():
    return random.choice(['true', 'false'])

def generate_bool_variable(ctx):
    if not ctx.bool_vars or random.random() < 0.3:
        return ctx.add_bool_var()
    return random.choice(ctx.bool_vars)

def generate_non_bool_term(ctx, sort, depth):
    if depth >= MAX_DEPTH:
        vars_of_sort = ctx.get_vars_of_sort(sort)
        if not vars_of_sort:
            return ctx.add_typed_var(sort)
        return random.choice(vars_of_sort)
    
    choice = random.randint(0, 3)
    
    if choice == 0:
        vars_of_sort = ctx.get_vars_of_sort(sort)
        if not vars_of_sort or random.random() < 0.3:
            return ctx.add_typed_var(sort)
        return random.choice(vars_of_sort)
    
    elif choice == 1:
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_non_bool_term(ctx, sort, depth + 1)
        else_branch = generate_non_bool_term(ctx, sort, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"
    
    elif choice == 2:
        arity = random.randint(0, 2)
        arg_sorts = [random.choice(ctx.sorts) for _ in range(arity)]
        funcs = ctx.get_funcs_of_signature(arg_sorts, sort)
        if not funcs or random.random() < 0.4:
            func = ctx.add_typed_func(arg_sorts, sort)
        else:
            func = random.choice(funcs)
        
        args = []
        for arg_sort in arg_sorts:
            if arg_sort == 'Bool':
                args.append(generate_bool_term(ctx, depth + 1))
            else:
                args.append(generate_non_bool_term(ctx, arg_sort, depth + 1))
        
        if args:
            return f"({func} {' '.join(args)})"
        return func
    
    else:
        term = generate_non_bool_term(ctx, sort, depth + 1)
        attr_count = random.randint(1, 2)
        attrs = []
        for _ in range(attr_count):
            key = ':' + generate_name('attr', 3)
            if random.random() < 0.5:
                attrs.append(key)
            else:
                val = random.choice(['42', 'true', generate_name('val', 3)])
                attrs.append(f"{key} {val}")
        return f"(! {term} {' '.join(attrs)})"

def generate_term(ctx, sort, depth):
    if sort == 'Bool':
        return generate_bool_term(ctx, depth)
    return generate_non_bool_term(ctx, sort, depth)

def generate_bool_term(ctx, depth=0):
    if depth >= MAX_DEPTH:
        if random.random() < 0.5:
            return generate_bool_constant()
        return generate_bool_variable(ctx)
    
    weights = [10, 15, 12, 12, 8, 8, 8, 8, 6]
    choice = random.choices(range(9), weights=weights)[0]
    
    if choice == 0:
        return generate_bool_constant()
    
    elif choice == 1:
        return generate_bool_variable(ctx)
    
    elif choice == 2:
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"
    
    elif choice == 3:
        num_args = random.randint(2, min(MAX_CHILDREN, 4))
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(=> {' '.join(args)})"
    
    elif choice == 4:
        num_args = random.randint(2, min(MAX_CHILDREN, 4))
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(and {' '.join(args)})"
    
    elif choice == 5:
        num_args = random.randint(2, min(MAX_CHILDREN, 4))
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(or {' '.join(args)})"
    
    elif choice == 6:
        num_args = random.randint(2, min(MAX_CHILDREN, 4))
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(xor {' '.join(args)})"
    
    elif choice == 7:
        sort = random.choice(ctx.sorts)
        num_args = random.randint(2, min(MAX_CHILDREN, 3))
        args = [generate_term(ctx, sort, depth + 1) for _ in range(num_args)]
        
        op = random.choice(['=', 'distinct'])
        return f"({op} {' '.join(args)})"
    
    else:
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_bool_term(ctx, depth + 1)
        else_branch = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_branch} {else_branch})"

def generate_core_formula_with_decls():
    ctx = Context()
    
    num_custom_sorts = random.randint(0, 3)
    for _ in range(num_custom_sorts):
        ctx.add_custom_sort()
    
    num_bool_vars = random.randint(2, 6)
    for _ in range(num_bool_vars):
        ctx.add_bool_var()
    
    num_typed_vars = random.randint(0, 4)
    for _ in range(num_typed_vars):
        sort = random.choice(ctx.sorts)
        if sort != 'Bool':
            ctx.add_typed_var(sort)
    
    num_funcs = random.randint(0, 3)
    for _ in range(num_funcs):
        arity = random.randint(0, 2)
        arg_sorts = [random.choice(ctx.sorts) for _ in range(arity)]
        ret_sort = random.choice(ctx.sorts)
        ctx.add_typed_func(arg_sorts, ret_sort)
    
    formula = generate_bool_term(ctx, 0)
    
    decls_str = '\n'.join(ctx.decls)
    
    return decls_str, formula