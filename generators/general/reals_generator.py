import random
import string

# ============================================================================
# SMT-LIB Keywords (reserved words that cannot be used as identifiers)
# ============================================================================
SMTLIB_KEYWORDS = {
    'and', 'or', 'not', 'xor', 'ite', 'let', 'forall', 'exists',
    'true', 'false', 'distinct', 'Bool', 'Real', 'Int', 'String',
    'assert', 'check-sat', 'declare-fun', 'declare-const', 'define-fun',
    'set-logic', 'set-option', 'get-model', 'get-value', 'push', 'pop',
    'as', 'par', 'match', 'case'
}

# ============================================================================
# Random Name Generation
# ============================================================================
def generate_random_name(min_length=5):
    """Generate a random lowercase alphabetic name of at least min_length characters."""
    length = random.randint(min_length, min_length + 5)
    while True:
        name = ''.join(random.choices(string.ascii_lowercase, k=length))
        if name not in SMTLIB_KEYWORDS:
            return name

# ============================================================================
# Context Manager for Tracking Declarations and Variables
# ============================================================================
class GenerationContext:
    def __init__(self):
        self.bool_vars = []
        self.real_vars = []
        self.declarations = []
        self.max_depth = random.randint(3, 6)
        self.current_depth = 0
        self.quantifier_depth = 0
        self.max_quantifier_depth = 2
        
    def add_bool_var(self, name):
        if name not in self.bool_vars:
            self.bool_vars.append(name)
            self.declarations.append(f"(declare-const {name} Bool)")
    
    def add_real_var(self, name):
        if name not in self.real_vars:
            self.real_vars.append(name)
            self.declarations.append(f"(declare-const {name} Real)")
    
    def get_decls_str(self):
        return '\n'.join(self.declarations)
    
    def enter_depth(self):
        self.current_depth += 1
    
    def exit_depth(self):
        self.current_depth -= 1
    
    def should_terminate(self):
        return self.current_depth >= self.max_depth
    
    def enter_quantifier(self):
        self.quantifier_depth += 1
    
    def exit_quantifier(self):
        self.quantifier_depth -= 1
    
    def can_use_quantifier(self):
        return self.quantifier_depth < self.max_quantifier_depth

# ============================================================================
# Real Term Generation
# ============================================================================
def generate_numeral():
    """Generate a numeral (non-negative integer) as a Real literal."""
    # Convert to Real by using decimal notation
    return f"{random.randint(0, 100)}.0"

def generate_decimal():
    """Generate a decimal literal."""
    int_part = random.randint(0, 100)
    frac_part = random.randint(1, 999)
    return f"{int_part}.{frac_part}"

def generate_real_literal():
    """Generate a Real literal (always with decimal point)."""
    if random.random() < 0.5:
        return generate_numeral()
    else:
        return generate_decimal()

def generate_real_term(ctx, local_vars=None):
    """Generate a Real-sorted term."""
    if local_vars is None:
        local_vars = {'Bool': [], 'Real': []}
    
    ctx.enter_depth()
    
    # Available real variables
    available_real_vars = ctx.real_vars + local_vars['Real']
    
    # Ensure we have at least one real variable
    if not available_real_vars and random.random() < 0.3:
        new_var = generate_random_name()
        ctx.add_real_var(new_var)
        available_real_vars = ctx.real_vars + local_vars['Real']
    
    if ctx.should_terminate():
        # Base case: literal or variable
        if available_real_vars and random.random() < 0.6:
            result = random.choice(available_real_vars)
        else:
            result = generate_real_literal()
    else:
        choices = []
        weights = []
        
        # Literals
        choices.append('literal')
        weights.append(20)
        
        # Variables
        if available_real_vars:
            choices.append('var')
            weights.append(25)
        
        # Unary negation
        choices.append('unary_neg')
        weights.append(10)
        
        # Binary operators
        choices.extend(['add', 'sub', 'mul', 'div'])
        weights.extend([15, 15, 10, 8])
        
        # ITE
        choices.append('ite')
        weights.append(10)
        
        # Let
        choices.append('let')
        weights.append(5)
        
        choice = random.choices(choices, weights=weights)[0]
        
        if choice == 'literal':
            result = generate_real_literal()
        elif choice == 'var':
            result = random.choice(available_real_vars)
        elif choice == 'unary_neg':
            arg = generate_real_term(ctx, local_vars)
            result = f"(- {arg})"
        elif choice in ['add', 'sub', 'mul', 'div']:
            op = {
                'add': '+',
                'sub': '-',
                'mul': '*',
                'div': '/'
            }[choice]
            num_args = random.randint(2, 4)
            args = [generate_real_term(ctx, local_vars) for _ in range(num_args)]
            result = f"({op} {' '.join(args)})"
        elif choice == 'ite':
            cond = generate_bool_term(ctx, local_vars)
            then_branch = generate_real_term(ctx, local_vars)
            else_branch = generate_real_term(ctx, local_vars)
            result = f"(ite {cond} {then_branch} {else_branch})"
        elif choice == 'let':
            num_bindings = random.randint(1, 2)
            bindings = []
            new_local_vars = {
                'Bool': local_vars['Bool'][:],
                'Real': local_vars['Real'][:]
            }
            for _ in range(num_bindings):
                var_name = generate_random_name()
                if random.random() < 0.7:
                    # Real binding
                    value = generate_real_term(ctx, local_vars)
                    bindings.append(f"({var_name} {value})")
                    new_local_vars['Real'].append(var_name)
                else:
                    # Bool binding
                    value = generate_bool_term(ctx, local_vars)
                    bindings.append(f"({var_name} {value})")
                    new_local_vars['Bool'].append(var_name)
            body = generate_real_term(ctx, new_local_vars)
            bindings_str = ' '.join(bindings)
            result = f"(let ({bindings_str}) {body})"
        else:
            result = generate_real_literal()
    
    ctx.exit_depth()
    return result

# ============================================================================
# Boolean Term Generation
# ============================================================================
def generate_comparison(ctx, local_vars=None):
    """Generate a comparison predicate."""
    if local_vars is None:
        local_vars = {'Bool': [], 'Real': []}
    
    ops = ['<=', '<', '>=', '>', '=', 'distinct']
    op = random.choice(ops)
    num_args = random.randint(2, 3)
    args = [generate_real_term(ctx, local_vars) for _ in range(num_args)]
    return f"({op} {' '.join(args)})"

def generate_bool_term(ctx, local_vars=None):
    """Generate a Boolean-sorted term."""
    if local_vars is None:
        local_vars = {'Bool': [], 'Real': []}
    
    ctx.enter_depth()
    
    # Available bool variables
    available_bool_vars = ctx.bool_vars + local_vars['Bool']
    
    # Ensure we have at least one bool variable
    if not available_bool_vars and random.random() < 0.2:
        new_var = generate_random_name()
        ctx.add_bool_var(new_var)
        available_bool_vars = ctx.bool_vars + local_vars['Bool']
    
    if ctx.should_terminate():
        # Base case: constant, variable, or comparison
        choices = ['true', 'false', 'comparison']
        if available_bool_vars:
            choices.append('var')
        choice = random.choice(choices)
        
        if choice == 'true':
            result = 'true'
        elif choice == 'false':
            result = 'false'
        elif choice == 'var':
            result = random.choice(available_bool_vars)
        else:
            result = generate_comparison(ctx, local_vars)
    else:
        choices = []
        weights = []
        
        # Constants
        choices.extend(['true', 'false'])
        weights.extend([8, 8])
        
        # Variables
        if available_bool_vars:
            choices.append('var')
            weights.append(12)
        
        # Comparisons
        choices.append('comparison')
        weights.append(20)
        
        # Logical operators
        choices.extend(['not', 'and', 'or', 'xor', 'implies'])
        weights.extend([10, 15, 15, 8, 8])
        
        # Equality and distinct
        choices.extend(['bool_eq', 'bool_distinct'])
        weights.extend([8, 6])
        
        # ITE
        choices.append('ite')
        weights.append(8)
        
        # Let
        choices.append('let')
        weights.append(5)
        
        # Quantifiers
        if ctx.can_use_quantifier():
            choices.extend(['forall', 'exists'])
            weights.extend([4, 4])
        
        choice = random.choices(choices, weights=weights)[0]
        
        if choice == 'true':
            result = 'true'
        elif choice == 'false':
            result = 'false'
        elif choice == 'var':
            result = random.choice(available_bool_vars)
        elif choice == 'comparison':
            result = generate_comparison(ctx, local_vars)
        elif choice == 'not':
            arg = generate_bool_term(ctx, local_vars)
            result = f"(not {arg})"
        elif choice == 'and':
            num_args = random.randint(2, 4)
            args = [generate_bool_term(ctx, local_vars) for _ in range(num_args)]
            result = f"(and {' '.join(args)})"
        elif choice == 'or':
            num_args = random.randint(2, 4)
            args = [generate_bool_term(ctx, local_vars) for _ in range(num_args)]
            result = f"(or {' '.join(args)})"
        elif choice == 'xor':
            arg1 = generate_bool_term(ctx, local_vars)
            arg2 = generate_bool_term(ctx, local_vars)
            result = f"(xor {arg1} {arg2})"
        elif choice == 'implies':
            num_args = random.randint(2, 3)
            args = [generate_bool_term(ctx, local_vars) for _ in range(num_args)]
            result = f"(=> {' '.join(args)})"
        elif choice == 'bool_eq':
            arg1 = generate_bool_term(ctx, local_vars)
            arg2 = generate_bool_term(ctx, local_vars)
            result = f"(= {arg1} {arg2})"
        elif choice == 'bool_distinct':
            num_args = random.randint(2, 3)
            args = [generate_bool_term(ctx, local_vars) for _ in range(num_args)]
            result = f"(distinct {' '.join(args)})"
        elif choice == 'ite':
            cond = generate_bool_term(ctx, local_vars)
            then_branch = generate_bool_term(ctx, local_vars)
            else_branch = generate_bool_term(ctx, local_vars)
            result = f"(ite {cond} {then_branch} {else_branch})"
        elif choice == 'let':
            num_bindings = random.randint(1, 2)
            bindings = []
            new_local_vars = {
                'Bool': local_vars['Bool'][:],
                'Real': local_vars['Real'][:]
            }
            for _ in range(num_bindings):
                var_name = generate_random_name()
                if random.random() < 0.5:
                    # Bool binding
                    value = generate_bool_term(ctx, local_vars)
                    bindings.append(f"({var_name} {value})")
                    new_local_vars['Bool'].append(var_name)
                else:
                    # Real binding
                    value = generate_real_term(ctx, local_vars)
                    bindings.append(f"({var_name} {value})")
                    new_local_vars['Real'].append(var_name)
            body = generate_bool_term(ctx, new_local_vars)
            bindings_str = ' '.join(bindings)
            result = f"(let ({bindings_str}) {body})"
        elif choice == 'forall':
            ctx.enter_quantifier()
            num_vars = random.randint(1, 2)
            sorted_vars = []
            new_local_vars = {
                'Bool': local_vars['Bool'][:],
                'Real': local_vars['Real'][:]
            }
            for _ in range(num_vars):
                var_name = generate_random_name()
                sort = random.choice(['Real', 'Bool'])
                sorted_vars.append(f"({var_name} {sort})")
                new_local_vars[sort].append(var_name)
            body = generate_bool_term(ctx, new_local_vars)
            sorted_vars_str = ' '.join(sorted_vars)
            result = f"(forall ({sorted_vars_str}) {body})"
            ctx.exit_quantifier()
        elif choice == 'exists':
            ctx.enter_quantifier()
            num_vars = random.randint(1, 2)
            sorted_vars = []
            new_local_vars = {
                'Bool': local_vars['Bool'][:],
                'Real': local_vars['Real'][:]
            }
            for _ in range(num_vars):
                var_name = generate_random_name()
                sort = random.choice(['Real', 'Bool'])
                sorted_vars.append(f"({var_name} {sort})")
                new_local_vars[sort].append(var_name)
            body = generate_bool_term(ctx, new_local_vars)
            sorted_vars_str = ' '.join(sorted_vars)
            result = f"(exists ({sorted_vars_str}) {body})"
            ctx.exit_quantifier()
        else:
            result = 'true'
    
    ctx.exit_depth()
    return result

# ============================================================================
# Main Generation Function
# ============================================================================
def generate_reals_formula_with_decls():
    """
    Generate a random Boolean formula in the Reals theory.
    
    Returns:
        tuple: (decls, formula) where decls is a string of declarations
               and formula is a Boolean term.
    """
    ctx = GenerationContext()
    
    # Pre-populate with some variables to ensure non-trivial formulas
    num_initial_bool_vars = random.randint(1, 3)
    num_initial_real_vars = random.randint(2, 4)
    
    for _ in range(num_initial_bool_vars):
        ctx.add_bool_var(generate_random_name())
    
    for _ in range(num_initial_real_vars):
        ctx.add_real_var(generate_random_name())
    
    # Generate the formula
    formula = generate_bool_term(ctx)
    
    # Get declarations
    decls = ctx.get_decls_str()
    
    return decls, formula