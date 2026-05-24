import random
import string

# ============================================================================
# SMT-LIB2 Keywords (reserved words to avoid in generated names)
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'assert', 'declare-fun', 'declare-const', 'declare-sort',
    'define-fun', 'define-sort', 'set-logic', 'check-sat', 'get-model',
    'push', 'pop', 'as', 'xor', 'implies', 'iff', 'par', 'lambda',
    'distinct', 'match', 'Bool', 'Int', 'Real', 'Array', 'BitVec',
    'partial-order', 'linear-order', 'tree-order', 'piecewise-linear-order',
    'transitive-closure', 'set-logic', 'set-option', 'get-info', 'exit'
}

# ============================================================================
# Name Generation
# ============================================================================
def generate_name(min_length=5):
    """Generate a random lowercase name of at least min_length characters, avoiding keywords."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and available symbols
# ============================================================================
class Context:
    def __init__(self):
        self.sorts = []
        self.constants = {}  # name -> sort
        self.functions = {}  # name -> (arg_sorts, return_sort)
        self.relations = {}  # name -> sort (binary relations on a specific sort)
        self.bound_vars = []  # stack of bound variable scopes [(name, sort), ...]
        
    def add_sort(self, sort_name):
        if sort_name not in self.sorts:
            self.sorts.append(sort_name)
    
    def add_constant(self, name, sort):
        self.constants[name] = sort
    
    def add_function(self, name, arg_sorts, return_sort):
        self.functions[name] = (arg_sorts, return_sort)
    
    def add_relation(self, name, sort):
        self.relations[name] = sort
    
    def push_bound_vars(self, vars_list):
        self.bound_vars.append(vars_list)
    
    def pop_bound_vars(self):
        if self.bound_vars:
            self.bound_vars.pop()
    
    def get_all_vars_of_sort(self, sort):
        """Return all available variables (bound + constants) of a given sort."""
        result = []
        for scope in self.bound_vars:
            for name, s in scope:
                if s == sort:
                    result.append(name)
        for name, s in self.constants.items():
            if s == sort:
                result.append(name)
        return result
    
    def get_functions_returning_sort(self, sort):
        """Return all functions that return the given sort."""
        return [name for name, (args, ret) in self.functions.items() if ret == sort]

# ============================================================================
# Declaration Generation
# ============================================================================
def generate_declarations(ctx, num_sorts, num_constants, num_functions, num_relations):
    """Generate random sorts, constants, functions, and relations."""
    decls = []
    
    # Generate sorts
    for _ in range(num_sorts):
        sort_name = generate_name()
        ctx.add_sort(sort_name)
        decls.append(f"(declare-sort {sort_name} 0)")
    
    # Generate constants
    for _ in range(num_constants):
        const_name = generate_name()
        sort = random.choice(ctx.sorts)
        ctx.add_constant(const_name, sort)
        decls.append(f"(declare-const {const_name} {sort})")
    
    # Generate functions
    for _ in range(num_functions):
        func_name = generate_name()
        arity = random.randint(1, 3)
        arg_sorts = [random.choice(ctx.sorts) for _ in range(arity)]
        return_sort = random.choice(ctx.sorts)
        ctx.add_function(func_name, arg_sorts, return_sort)
        args_str = ' '.join(arg_sorts)
        decls.append(f"(declare-fun {func_name} ({args_str}) {return_sort})")
    
    # Generate binary relations (user-defined)
    for _ in range(num_relations):
        rel_name = generate_name()
        sort = random.choice(ctx.sorts)
        ctx.add_relation(rel_name, sort)
        ctx.add_function(rel_name, [sort, sort], 'Bool')
        decls.append(f"(declare-fun {rel_name} ({sort} {sort}) Bool)")
    
    return '\n'.join(decls)

# ============================================================================
# Term Generation
# ============================================================================
def generate_term(ctx, sort, depth=0, max_depth=3):
    """Generate a term of the given sort."""
    if depth >= max_depth:
        # Base case: return a variable or constant
        vars = ctx.get_all_vars_of_sort(sort)
        if vars:
            return random.choice(vars)
        # Fallback: create a fresh constant if needed
        const_name = generate_name()
        ctx.add_constant(const_name, sort)
        return const_name
    
    # Choose between variable/constant or function application
    choice = random.random()
    
    if choice < 0.5:
        # Return a variable or constant
        vars = ctx.get_all_vars_of_sort(sort)
        if vars:
            return random.choice(vars)
        const_name = generate_name()
        ctx.add_constant(const_name, sort)
        return const_name
    else:
        # Try function application
        funcs = ctx.get_functions_returning_sort(sort)
        if funcs:
            func = random.choice(funcs)
            arg_sorts, _ = ctx.functions[func]
            args = [generate_term(ctx, s, depth + 1, max_depth) for s in arg_sorts]
            return f"({func} {' '.join(args)})"
        else:
            # No function available, return variable/constant
            vars = ctx.get_all_vars_of_sort(sort)
            if vars:
                return random.choice(vars)
            const_name = generate_name()
            ctx.add_constant(const_name, sort)
            return const_name

# ============================================================================
# Boolean Term Generation (CFG-based)
# ============================================================================
def generate_bool_term(ctx, depth=0, max_depth=4):
    """Generate a Boolean term following the CFG."""
    if depth >= max_depth:
        # Base case: return a literal or simple relation application
        return random.choice(['true', 'false'])
    
    # Choose a production
    productions = [
        'relation_application',
        'equality',
        'boolean_literal',
        'boolean_connective',
        'quantified_formula',
        'let_binding',
        'ite_expression'
    ]
    
    # Weight to encourage diversity
    weights = [3, 2, 1, 4, 2, 1, 2]
    production = random.choices(productions, weights=weights, k=1)[0]
    
    if production == 'relation_application':
        return generate_relation_application(ctx, depth)
    elif production == 'equality':
        return generate_equality(ctx, depth)
    elif production == 'boolean_literal':
        return random.choice(['true', 'false'])
    elif production == 'boolean_connective':
        return generate_boolean_connective(ctx, depth)
    elif production == 'quantified_formula':
        return generate_quantified_formula(ctx, depth)
    elif production == 'let_binding':
        return generate_let_binding(ctx, depth)
    elif production == 'ite_expression':
        return generate_ite_expression(ctx, depth)
    else:
        return 'true'

def generate_relation_application(ctx, depth):
    """Generate a relation application."""
    # Only use user-defined relations
    if not ctx.relations:
        return 'true'
    
    rel_name = random.choice(list(ctx.relations.keys()))
    sort = ctx.relations[rel_name]
    
    # Generate two terms of the appropriate sort
    term1 = generate_term(ctx, sort, depth + 1)
    term2 = generate_term(ctx, sort, depth + 1)
    
    return f"({rel_name} {term1} {term2})"

def generate_equality(ctx, depth):
    """Generate an equality term."""
    if not ctx.sorts:
        return 'true'
    sort = random.choice(ctx.sorts)
    term1 = generate_term(ctx, sort, depth + 1)
    term2 = generate_term(ctx, sort, depth + 1)
    return f"(= {term1} {term2})"

def generate_boolean_connective(ctx, depth):
    """Generate a Boolean connective."""
    connectives = ['not', 'and', 'or', 'implies', 'xor']
    conn = random.choice(connectives)
    
    if conn == 'not':
        sub_term = generate_bool_term(ctx, depth + 1)
        return f"(not {sub_term})"
    elif conn == 'and':
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(and {' '.join(args)})"
    elif conn == 'or':
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(or {' '.join(args)})"
    elif conn == 'implies':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(=> {arg1} {arg2})"
    elif conn == 'xor':
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(xor {' '.join(args)})"
    else:
        return 'true'

def generate_quantified_formula(ctx, depth):
    """Generate a quantified formula."""
    quantifier = random.choice(['forall', 'exists'])
    num_vars = random.randint(1, 3)
    
    if not ctx.sorts:
        return 'true'
    
    vars_list = []
    for _ in range(num_vars):
        var_name = generate_name()
        sort = random.choice(ctx.sorts)
        vars_list.append((var_name, sort))
    
    vars_str = ' '.join([f"({name} {sort})" for name, sort in vars_list])
    
    ctx.push_bound_vars(vars_list)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_bound_vars()
    
    return f"({quantifier} ({vars_str}) {body})"

def generate_let_binding(ctx, depth):
    """Generate a let binding."""
    num_bindings = random.randint(1, 2)
    
    if not ctx.sorts:
        return 'true'
    
    bindings = []
    bound_vars = []
    for _ in range(num_bindings):
        var_name = generate_name()
        sort = random.choice(ctx.sorts)
        term = generate_term(ctx, sort, depth + 1)
        bindings.append(f"({var_name} {term})")
        bound_vars.append((var_name, sort))
    
    bindings_str = ' '.join(bindings)
    
    ctx.push_bound_vars(bound_vars)
    body = generate_bool_term(ctx, depth + 1)
    ctx.pop_bound_vars()
    
    return f"(let ({bindings_str}) {body})"

def generate_ite_expression(ctx, depth):
    """Generate an if-then-else expression."""
    cond = generate_bool_term(ctx, depth + 1)
    then_branch = generate_bool_term(ctx, depth + 1)
    else_branch = generate_bool_term(ctx, depth + 1)
    return f"(ite {cond} {then_branch} {else_branch})"

# ============================================================================
# Main Generation Function
# ============================================================================
def generate_z3relation_formula_with_decls():
    """Generate a random z3_relation formula with declarations."""
    ctx = Context()
    
    # Randomize the number of declarations
    num_sorts = random.randint(1, 3)
    num_constants = random.randint(2, 6)
    num_functions = random.randint(0, 3)
    num_relations = random.randint(1, 4)
    
    # Generate declarations
    decls = generate_declarations(ctx, num_sorts, num_constants, num_functions, num_relations)
    
    # Generate formula
    max_depth = random.randint(3, 5)
    formula = generate_bool_term(ctx, depth=0, max_depth=max_depth)
    
    return decls, formula