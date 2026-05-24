import random
import string

# ============================================================================
# Configuration and Constants
# ============================================================================

MAX_DEPTH = 5
MAX_CHILDREN = 4
MIN_NAME_LENGTH = 5
MAX_NAME_LENGTH = 10

SMT_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'true', 'false', 'let', 'forall', 'exists',
    'distinct', 'assert', 'check-sat', 'declare-fun', 'declare-const', 'declare-sort',
    'declare-datatype', 'declare-datatypes', 'define-fun', 'define-sort',
    'get-model', 'get-value', 'push', 'pop', 'set-logic', 'set-option',
    'Bool', 'Int', 'Real', 'String', 'Array', 'BitVec',
    'as', 'is', 'update', 'tuple', 'select', 'project', 'unit',
    'par', 'match', 'case', 'default'
}

# ============================================================================
# Name Generation
# ============================================================================

def generate_name(prefix=''):
    length = random.randint(MIN_NAME_LENGTH, MAX_NAME_LENGTH)
    while True:
        name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMT_KEYWORDS and len(name) >= MIN_NAME_LENGTH:
            return name

# ============================================================================
# Context Management
# ============================================================================

class Context:
    def __init__(self):
        self.datatypes = []
        self.constructors = {}
        self.selectors = {}
        self.bool_vars = []
        self.datatype_vars = {}
        self.bound_vars = []
        
    def add_datatype(self, dt_name, constructors_info):
        self.datatypes.append(dt_name)
        for cons_name, selectors_info in constructors_info:
            if cons_name not in self.constructors:
                self.constructors[cons_name] = (dt_name, selectors_info)
            for sel_name, sel_sort in selectors_info:
                if sel_name not in self.selectors:
                    self.selectors[sel_name] = (dt_name, sel_sort)
    
    def add_bool_var(self, var_name):
        self.bool_vars.append(var_name)
    
    def add_datatype_var(self, var_name, sort):
        if sort not in self.datatype_vars:
            self.datatype_vars[sort] = []
        self.datatype_vars[sort].append(var_name)
    
    def get_random_bool_var(self):
        all_bool = self.bool_vars + [v for v, _ in self.bound_vars if _ == 'Bool']
        return random.choice(all_bool) if all_bool else None
    
    def get_random_datatype_var(self, sort):
        vars_of_sort = self.datatype_vars.get(sort, [])
        bound_of_sort = [v for v, s in self.bound_vars if s == sort]
        all_vars = vars_of_sort + bound_of_sort
        return random.choice(all_vars) if all_vars else None
    
    def get_random_constructor(self, dt_name=None):
        if dt_name:
            candidates = [(c, info) for c, info in self.constructors.items() if info[0] == dt_name]
        else:
            candidates = list(self.constructors.items())
        return random.choice(candidates) if candidates else None
    
    def get_random_selector(self, dt_name=None):
        if dt_name:
            candidates = [(s, info) for s, info in self.selectors.items() if info[0] == dt_name]
        else:
            candidates = list(self.selectors.items())
        return random.choice(candidates) if candidates else None
    
    def push_bound_vars(self, vars_list):
        self.bound_vars.extend(vars_list)
    
    def pop_bound_vars(self, count):
        self.bound_vars = self.bound_vars[:-count]

# ============================================================================
# Declaration Generation
# ============================================================================

def generate_declarations(ctx):
    decls = []
    
    # Generate datatypes
    num_datatypes = random.randint(1, 3)
    for _ in range(num_datatypes):
        dt_name = generate_name('dt')
        num_constructors = random.randint(1, 3)
        constructors_info = []
        
        # Ensure at least one constructor has no recursive references (well-founded)
        has_base_case = False
        
        for i in range(num_constructors):
            cons_name = generate_name('cons')
            
            # First constructor should be a base case
            if i == 0:
                num_selectors = random.randint(0, 2)
                selectors_info = []
                for _ in range(num_selectors):
                    sel_name = generate_name('sel')
                    sel_sort = random.choice(['Bool', 'Int'])
                    selectors_info.append((sel_name, sel_sort))
                has_base_case = True
            else:
                num_selectors = random.randint(0, 3)
                selectors_info = []
                for _ in range(num_selectors):
                    sel_name = generate_name('sel')
                    # Allow recursive references only if we have a base case
                    if has_base_case and random.random() < 0.3:
                        sel_sort = dt_name
                    else:
                        sel_sort = random.choice(['Bool', 'Int'])
                    selectors_info.append((sel_name, sel_sort))
            
            constructors_info.append((cons_name, selectors_info))
        
        ctx.add_datatype(dt_name, constructors_info)
        
        # Format datatype declaration
        cons_decls = []
        for cons_name, selectors_info in constructors_info:
            if selectors_info:
                sel_strs = [f'({sel_name} {sel_sort})' for sel_name, sel_sort in selectors_info]
                cons_decls.append(f'({cons_name} {" ".join(sel_strs)})')
            else:
                cons_decls.append(f'({cons_name})')
        
        decls.append(f'(declare-datatype {dt_name} ({" ".join(cons_decls)}))')
    
    # Generate Boolean variables
    num_bool_vars = random.randint(2, 5)
    for _ in range(num_bool_vars):
        var_name = generate_name('bvar')
        ctx.add_bool_var(var_name)
        decls.append(f'(declare-const {var_name} Bool)')
    
    # Generate datatype variables
    for dt_name in ctx.datatypes:
        num_vars = random.randint(1, 3)
        for _ in range(num_vars):
            var_name = generate_name('dvar')
            ctx.add_datatype_var(var_name, dt_name)
            decls.append(f'(declare-const {var_name} {dt_name})')
    
    return '\n'.join(decls)

# ============================================================================
# Term Generation
# ============================================================================

def generate_bool_term(ctx, depth=0):
    if depth >= MAX_DEPTH:
        return generate_bool_leaf(ctx)
    
    choices = ['leaf', 'tester', 'equality', 'not', 'and', 'or', 'xor', 'implies', 
               'ite', 'distinct', 'quantifier', 'let']
    weights = [20, 10, 10, 8, 8, 8, 5, 5, 8, 5, 3, 3]
    
    if depth > MAX_DEPTH // 2:
        weights[0] *= 3
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'leaf':
        return generate_bool_leaf(ctx)
    elif choice == 'tester':
        return generate_tester_term(ctx, depth)
    elif choice == 'equality':
        return generate_equality(ctx, depth)
    elif choice == 'not':
        return f'(not {generate_bool_term(ctx, depth + 1)})'
    elif choice == 'and':
        n = random.randint(2, min(MAX_CHILDREN, 4))
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f'(and {" ".join(terms)})'
    elif choice == 'or':
        n = random.randint(2, min(MAX_CHILDREN, 4))
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f'(or {" ".join(terms)})'
    elif choice == 'xor':
        t1 = generate_bool_term(ctx, depth + 1)
        t2 = generate_bool_term(ctx, depth + 1)
        return f'(xor {t1} {t2})'
    elif choice == 'implies':
        n = random.randint(2, min(MAX_CHILDREN, 3))
        terms = [generate_bool_term(ctx, depth + 1) for _ in range(n)]
        return f'(=> {" ".join(terms)})'
    elif choice == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_bool_term(ctx, depth + 1)
        else_branch = generate_bool_term(ctx, depth + 1)
        return f'(ite {cond} {then_branch} {else_branch})'
    elif choice == 'distinct':
        if ctx.datatypes:
            dt = random.choice(ctx.datatypes)
            n = random.randint(2, min(MAX_CHILDREN, 3))
            terms = [generate_datatype_term(ctx, dt, depth + 1) for _ in range(n)]
            return f'(distinct {" ".join(terms)})'
        return generate_bool_leaf(ctx)
    elif choice == 'quantifier':
        return generate_quantified_formula(ctx, depth)
    elif choice == 'let':
        return generate_let_bool(ctx, depth)
    
    return generate_bool_leaf(ctx)

def generate_bool_leaf(ctx):
    choices = ['true', 'false', 'var']
    weights = [5, 5, 15]
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'true':
        return 'true'
    elif choice == 'false':
        return 'false'
    else:
        var = ctx.get_random_bool_var()
        return var if var else random.choice(['true', 'false'])

def generate_tester_term(ctx, depth):
    if not ctx.constructors or not ctx.datatypes:
        return generate_bool_leaf(ctx)
    
    cons_name, (dt_name, _) = ctx.get_random_constructor()
    dt_term = generate_datatype_term(ctx, dt_name, depth + 1)
    return f'((_ is {cons_name}) {dt_term})'

def generate_equality(ctx, depth):
    if not ctx.datatypes:
        return generate_bool_leaf(ctx)
    
    dt = random.choice(ctx.datatypes)
    n = random.randint(2, min(MAX_CHILDREN, 3))
    terms = [generate_datatype_term(ctx, dt, depth + 1) for _ in range(n)]
    return f'(= {" ".join(terms)})'

def generate_quantified_formula(ctx, depth):
    quantifier = random.choice(['forall', 'exists'])
    num_vars = random.randint(1, 2)
    sorted_vars = []
    bound_vars_list = []
    
    for _ in range(num_vars):
        var_name = generate_name('qvar')
        sort = random.choice(['Bool'] + ctx.datatypes)
        sorted_vars.append(f'({var_name} {sort})')
        bound_vars_list.append((var_name, sort))
    
    ctx.push_bound_vars(bound_vars_list)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_bound_vars(len(bound_vars_list))
    
    return f'({quantifier} ({" ".join(sorted_vars)}) {body})'

def generate_let_bool(ctx, depth):
    num_bindings = random.randint(1, 2)
    bindings = []
    bound_vars_list = []
    
    for _ in range(num_bindings):
        var_name = generate_name('lvar')
        if random.choice([True, False]):
            value = generate_bool_term(ctx, depth + 1)
            sort = 'Bool'
        else:
            if ctx.datatypes:
                sort = random.choice(ctx.datatypes)
                value = generate_datatype_term(ctx, sort, depth + 1)
            else:
                value = generate_bool_term(ctx, depth + 1)
                sort = 'Bool'
        
        bindings.append(f'({var_name} {value})')
        bound_vars_list.append((var_name, sort))
    
    ctx.push_bound_vars(bound_vars_list)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_bound_vars(len(bound_vars_list))
    
    return f'(let ({" ".join(bindings)}) {body})'

def generate_datatype_term(ctx, dt_name, depth=0):
    if depth >= MAX_DEPTH:
        return generate_datatype_leaf(ctx, dt_name)
    
    choices = ['leaf', 'constructor', 'selector', 'updater', 'ite', 'let']
    weights = [15, 12, 8, 5, 6, 3]
    
    if depth > MAX_DEPTH // 2:
        weights[0] *= 2
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'leaf':
        return generate_datatype_leaf(ctx, dt_name)
    elif choice == 'constructor':
        return generate_constructor_app(ctx, dt_name, depth)
    elif choice == 'selector':
        return generate_selector_app(ctx, dt_name, depth)
    elif choice == 'updater':
        return generate_updater_app(ctx, dt_name, depth)
    elif choice == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_branch = generate_datatype_term(ctx, dt_name, depth + 1)
        else_branch = generate_datatype_term(ctx, dt_name, depth + 1)
        return f'(ite {cond} {then_branch} {else_branch})'
    elif choice == 'let':
        return generate_let_datatype(ctx, dt_name, depth)
    
    return generate_datatype_leaf(ctx, dt_name)

def generate_datatype_leaf(ctx, dt_name):
    var = ctx.get_random_datatype_var(dt_name)
    if var:
        return var
    
    # Generate a simple constructor (base case only)
    cons_info = ctx.get_random_constructor(dt_name)
    if cons_info:
        cons_name, (_, selectors_info) = cons_info
        if not selectors_info:
            return cons_name
        # Only use constructors with non-recursive arguments
        non_recursive = all(sel_sort != dt_name for _, sel_sort in selectors_info)
        if non_recursive:
            args = []
            for _, sel_sort in selectors_info:
                if sel_sort == 'Bool':
                    args.append(random.choice(['true', 'false']))
                elif sel_sort == 'Int':
                    args.append(str(random.randint(-10, 10)))
            if args:
                return f'({cons_name} {" ".join(args)})'
            else:
                return cons_name
    
    # Fallback to variable or simple constructor
    return var if var else cons_name if cons_info else generate_name("cons")

def generate_constructor_app(ctx, dt_name, depth):
    cons_info = ctx.get_random_constructor(dt_name)
    if not cons_info:
        return generate_datatype_leaf(ctx, dt_name)
    
    cons_name, (_, selectors_info) = cons_info
    
    if not selectors_info:
        return cons_name
    
    args = []
    for _, sel_sort in selectors_info:
        if sel_sort == 'Bool':
            args.append(generate_bool_term(ctx, depth + 1))
        elif sel_sort == 'Int':
            args.append(str(random.randint(-10, 10)))
        elif sel_sort in ctx.datatypes:
            args.append(generate_datatype_term(ctx, sel_sort, depth + 1))
        else:
            args.append(str(random.randint(0, 5)))
    
    return f'({cons_name} {" ".join(args)})'

def generate_selector_app(ctx, dt_name, depth):
    # Get selector that belongs to dt_name
    sel_info = ctx.get_random_selector(dt_name)
    if not sel_info:
        return generate_datatype_leaf(ctx, dt_name)
    
    sel_name, (sel_dt, sel_sort) = sel_info
    dt_term = generate_datatype_term(ctx, sel_dt, depth + 1)
    
    # Return type should match sel_sort, but we're generating dt_name
    # Only use if return type matches what we need
    if sel_sort == dt_name:
        return f'({sel_name} {dt_term})'
    else:
        return generate_datatype_leaf(ctx, dt_name)

def generate_updater_app(ctx, dt_name, depth):
    # Get selector that belongs to dt_name
    sel_info = ctx.get_random_selector(dt_name)
    if not sel_info:
        return generate_datatype_leaf(ctx, dt_name)
    
    sel_name, (sel_dt, sel_sort) = sel_info
    
    # Updater returns the same type as input
    if sel_dt != dt_name:
        return generate_datatype_leaf(ctx, dt_name)
    
    dt_term = generate_datatype_term(ctx, dt_name, depth + 1)
    
    if sel_sort == 'Bool':
        new_val = generate_bool_term(ctx, depth + 1)
    elif sel_sort == 'Int':
        new_val = str(random.randint(-10, 10))
    elif sel_sort in ctx.datatypes:
        new_val = generate_datatype_term(ctx, sel_sort, depth + 1)
    else:
        new_val = str(random.randint(0, 5))
    
    return f'((_ update {sel_name}) {dt_term} {new_val})'

def generate_let_datatype(ctx, dt_name, depth):
    num_bindings = random.randint(1, 2)
    bindings = []
    bound_vars_list = []
    
    for _ in range(num_bindings):
        var_name = generate_name('lvar')
        if random.choice([True, False]) and ctx.datatypes:
            sort = random.choice(ctx.datatypes)
            value = generate_datatype_term(ctx, sort, depth + 1)
        else:
            value = generate_bool_term(ctx, depth + 1)
            sort = 'Bool'
        
        bindings.append(f'({var_name} {value})')
        bound_vars_list.append((var_name, sort))
    
    ctx.push_bound_vars(bound_vars_list)
    body = generate_datatype_term(ctx, dt_name, depth + 1)
    ctx.pop_bound_vars(len(bound_vars_list))
    
    return f'(let ({" ".join(bindings)}) {body})'

# ============================================================================
# Main Generation Function
# ============================================================================

def generate_datatypes_formula_with_decls():
    ctx = Context()
    decls = generate_declarations(ctx)
    formula = generate_bool_term(ctx, depth=0)
    return decls, formula