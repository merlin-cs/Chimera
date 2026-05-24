import random
import string

# ============================================================================
# SMT-LIB2 Keywords to avoid
# ============================================================================
SMTLIB_KEYWORDS = {
    'true', 'false', 'not', 'and', 'or', 'xor', 'ite', 'forall', 'exists',
    'let', 'match', 'assert', 'declare-fun', 'declare-const', 'declare-sort',
    'define-fun', 'define-sort', 'set-logic', 'set-option', 'check-sat',
    'get-model', 'get-value', 'push', 'pop', 'exit', 'Bool', 'Int', 'Real',
    'Array', 'select', 'store', 'distinct', 'as', 'par', '_'
}

# ============================================================================
# Random name generation
# ============================================================================
def generate_random_name(min_len=5, max_len=10):
    """Generate a random lowercase name that is not an SMT-LIB keyword."""
    while True:
        length = random.randint(min_len, max_len)
        name = ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context for tracking declarations and depth
# ============================================================================
class GeneratorContext:
    def __init__(self, max_depth=5):
        self.max_depth = max_depth
        self.bool_vars = []
        self.element_vars = {}  # sort -> [var_names]
        self.array_vars = {}    # (index_sort, elem_sort) -> [var_names]
        self.element_sorts = ['Int', 'Real', 'Bool']
        self.user_defined_sorts = []
        
    def add_bool_var(self, name):
        self.bool_vars.append(name)
    
    def add_element_var(self, name, sort):
        if sort not in self.element_vars:
            self.element_vars[sort] = []
        self.element_vars[sort].append(name)
    
    def add_array_var(self, name, index_sort, elem_sort):
        key = (index_sort, elem_sort)
        if key not in self.array_vars:
            self.array_vars[key] = []
        self.array_vars[key].append(name)
    
    def get_random_bool_var(self):
        if self.bool_vars:
            return random.choice(self.bool_vars)
        return None
    
    def get_random_element_var(self, sort):
        if sort in self.element_vars and self.element_vars[sort]:
            return random.choice(self.element_vars[sort])
        return None
    
    def get_random_array_var(self, index_sort, elem_sort):
        key = (index_sort, elem_sort)
        if key in self.array_vars and self.array_vars[key]:
            return random.choice(self.array_vars[key])
        return None
    
    def get_random_element_sort(self):
        return random.choice(self.element_sorts)
    
    def get_all_element_sorts(self):
        return self.element_sorts.copy()

# ============================================================================
# Declaration generation
# ============================================================================
def generate_declarations(ctx):
    """Generate variable declarations based on context."""
    decls = []
    
    # Declare Bool variables
    for var in ctx.bool_vars:
        decls.append(f"(declare-const {var} Bool)")
    
    # Declare element variables
    for sort, vars in ctx.element_vars.items():
        for var in vars:
            decls.append(f"(declare-const {var} {sort})")
    
    # Declare array variables
    for (idx_sort, elem_sort), vars in ctx.array_vars.items():
        for var in vars:
            decls.append(f"(declare-const {var} (Array {idx_sort} {elem_sort}))")
    
    return '\n'.join(decls)

# ============================================================================
# Initialize context with random variables
# ============================================================================
def initialize_context():
    """Create a context with random variables."""
    ctx = GeneratorContext(max_depth=random.randint(3, 6))
    
    # Add Bool variables
    num_bool_vars = random.randint(2, 5)
    for _ in range(num_bool_vars):
        ctx.add_bool_var(generate_random_name())
    
    # Add element variables for different sorts
    for sort in ['Int', 'Real', 'Bool']:
        num_vars = random.randint(2, 4)
        for _ in range(num_vars):
            ctx.add_element_var(generate_random_name(), sort)
    
    # Add array variables with various index/element sort combinations
    num_array_types = random.randint(2, 4)
    for _ in range(num_array_types):
        idx_sort = random.choice(['Int', 'Real', 'Bool'])
        elem_sort = random.choice(['Int', 'Real', 'Bool'])
        num_arrays = random.randint(1, 3)
        for _ in range(num_arrays):
            ctx.add_array_var(generate_random_name(), idx_sort, elem_sort)
    
    return ctx

# ============================================================================
# Element constant generation
# ============================================================================
def generate_element_constant(sort):
    """Generate a constant of the given sort."""
    if sort == 'Int':
        return str(random.randint(-100, 100))
    elif sort == 'Real':
        num = random.randint(0, 100)
        denom = random.randint(1, 10)
        return f"{num}.{denom}"
    elif sort == 'Bool':
        return random.choice(['true', 'false'])
    else:
        # For user-defined sorts, generate a symbol
        return generate_random_name()

# ============================================================================
# Element term generation
# ============================================================================
def generate_element_term(ctx, sort, depth=0):
    """Generate an element term of the given sort."""
    if depth >= ctx.max_depth:
        # Base case: variable or constant
        var = ctx.get_random_element_var(sort)
        if var and random.random() < 0.7:
            return var
        return generate_element_constant(sort)
    
    choices = ['var', 'const', 'select', 'ite']
    weights = [0.3, 0.2, 0.3, 0.2]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'var':
        var = ctx.get_random_element_var(sort)
        if var:
            return var
        return generate_element_constant(sort)
    
    elif choice == 'const':
        return generate_element_constant(sort)
    
    elif choice == 'select':
        # Find an array with element sort matching our target sort
        matching_arrays = []
        for (idx_sort, elem_sort), vars in ctx.array_vars.items():
            if elem_sort == sort and vars:
                matching_arrays.extend([(v, idx_sort) for v in vars])
        
        if matching_arrays:
            array_var, idx_sort = random.choice(matching_arrays)
            index = generate_element_term(ctx, idx_sort, depth + 1)
            return f"(select {array_var} {index})"
        else:
            return generate_element_constant(sort)
    
    elif choice == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_element_term(ctx, sort, depth + 1)
        else_term = generate_element_term(ctx, sort, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"
    
    return generate_element_constant(sort)

# ============================================================================
# Array term generation
# ============================================================================
def generate_array_term(ctx, index_sort, elem_sort, depth=0):
    """Generate an array term with given index and element sorts."""
    if depth >= ctx.max_depth:
        var = ctx.get_random_array_var(index_sort, elem_sort)
        if var:
            return var
        # Fallback: create a simple array variable name (shouldn't happen)
        return generate_random_name()
    
    choices = ['var', 'store', 'ite']
    weights = [0.4, 0.4, 0.2]
    
    choice = random.choices(choices, weights=weights)[0]
    
    if choice == 'var':
        var = ctx.get_random_array_var(index_sort, elem_sort)
        if var:
            return var
        return generate_random_name()
    
    elif choice == 'store':
        base_array = generate_array_term(ctx, index_sort, elem_sort, depth + 1)
        index = generate_element_term(ctx, index_sort, depth + 1)
        value = generate_element_term(ctx, elem_sort, depth + 1)
        return f"(store {base_array} {index} {value})"
    
    elif choice == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_array = generate_array_term(ctx, index_sort, elem_sort, depth + 1)
        else_array = generate_array_term(ctx, index_sort, elem_sort, depth + 1)
        return f"(ite {cond} {then_array} {else_array})"
    
    var = ctx.get_random_array_var(index_sort, elem_sort)
    if var:
        return var
    return generate_random_name()

# ============================================================================
# General term generation
# ============================================================================
def generate_term(ctx, depth=0):
    """Generate a general term (element or array)."""
    if random.random() < 0.7:
        # Generate element term
        sort = ctx.get_random_element_sort()
        return generate_element_term(ctx, sort, depth)
    else:
        # Generate array term
        if ctx.array_vars:
            key = random.choice(list(ctx.array_vars.keys()))
            idx_sort, elem_sort = key
            return generate_array_term(ctx, idx_sort, elem_sort, depth)
        else:
            sort = ctx.get_random_element_sort()
            return generate_element_term(ctx, sort, depth)

# ============================================================================
# Boolean term generation
# ============================================================================
def generate_bool_term(ctx, depth=0):
    """Generate a Boolean term."""
    if depth >= ctx.max_depth:
        # Base case: true, false, or bool variable
        choices = ['true', 'false', 'var']
        choice = random.choice(choices)
        if choice == 'var':
            var = ctx.get_random_bool_var()
            if var:
                return var
        return random.choice(['true', 'false'])
    
    # Choose operator with weights to ensure diversity
    operators = ['true', 'false', 'var', 'not', 'and', 'or', 'implies', 
                 'xor', 'eq', 'distinct', 'ite', 'quantified']
    weights = [0.05, 0.05, 0.1, 0.1, 0.15, 0.15, 0.1, 0.05, 0.1, 0.05, 0.05, 0.05]
    
    op = random.choices(operators, weights=weights)[0]
    
    if op == 'true':
        return 'true'
    
    elif op == 'false':
        return 'false'
    
    elif op == 'var':
        var = ctx.get_random_bool_var()
        if var:
            return var
        return random.choice(['true', 'false'])
    
    elif op == 'not':
        arg = generate_bool_term(ctx, depth + 1)
        return f"(not {arg})"
    
    elif op == 'and':
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(and {' '.join(args)})"
    
    elif op == 'or':
        num_args = random.randint(2, 4)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(or {' '.join(args)})"
    
    elif op == 'implies':
        num_args = random.randint(2, 3)
        args = [generate_bool_term(ctx, depth + 1) for _ in range(num_args)]
        return f"(=> {' '.join(args)})"
    
    elif op == 'xor':
        arg1 = generate_bool_term(ctx, depth + 1)
        arg2 = generate_bool_term(ctx, depth + 1)
        return f"(xor {arg1} {arg2})"
    
    elif op == 'eq':
        num_args = random.randint(2, 3)
        # Decide if comparing arrays or elements
        if random.random() < 0.3 and ctx.array_vars:
            # Compare arrays
            key = random.choice(list(ctx.array_vars.keys()))
            idx_sort, elem_sort = key
            args = [generate_array_term(ctx, idx_sort, elem_sort, depth + 1) 
                    for _ in range(num_args)]
        else:
            # Compare elements
            sort = ctx.get_random_element_sort()
            args = [generate_element_term(ctx, sort, depth + 1) 
                    for _ in range(num_args)]
        return f"(= {' '.join(args)})"
    
    elif op == 'distinct':
        num_args = random.randint(2, 3)
        sort = ctx.get_random_element_sort()
        args = [generate_element_term(ctx, sort, depth + 1) 
                for _ in range(num_args)]
        return f"(distinct {' '.join(args)})"
    
    elif op == 'ite':
        cond = generate_bool_term(ctx, depth + 1)
        then_term = generate_bool_term(ctx, depth + 1)
        else_term = generate_bool_term(ctx, depth + 1)
        return f"(ite {cond} {then_term} {else_term})"
    
    elif op == 'quantified':
        if depth < ctx.max_depth - 1:
            return generate_quantified_term(ctx, depth)
        else:
            return generate_bool_term(ctx, depth + 1)
    
    return 'true'

# ============================================================================
# Quantified term generation
# ============================================================================
def generate_quantified_term(ctx, depth=0):
    """Generate a quantified Boolean term."""
    quantifier = random.choice(['forall', 'exists'])
    
    # Generate sorted variables
    num_vars = random.randint(1, 3)
    sorted_vars = []
    var_names = []
    
    for _ in range(num_vars):
        var_name = generate_random_name()
        var_names.append(var_name)
        
        # Choose sort for this variable
        if random.random() < 0.7:
            # Element sort
            sort = ctx.get_random_element_sort()
            sorted_vars.append(f"({var_name} {sort})")
        else:
            # Array sort
            if ctx.array_vars:
                key = random.choice(list(ctx.array_vars.keys()))
                idx_sort, elem_sort = key
                sorted_vars.append(f"({var_name} (Array {idx_sort} {elem_sort}))")
            else:
                sort = ctx.get_random_element_sort()
                sorted_vars.append(f"({var_name} {sort})")
    
    sorted_vars_str = ' '.join(sorted_vars)
    
    # Generate body with increased depth limit
    body = generate_bool_term(ctx, depth + 1)
    
    return f"({quantifier} ({sorted_vars_str}) {body})"

# ============================================================================
# Main generation function
# ============================================================================
def generate_arrayex_formula_with_decls():
    """Generate a random ArraysEx formula with declarations."""
    ctx = initialize_context()
    
    # Generate the main Boolean formula
    formula = generate_bool_term(ctx, depth=0)
    
    # Generate declarations
    decls = generate_declarations(ctx)
    
    return decls, formula