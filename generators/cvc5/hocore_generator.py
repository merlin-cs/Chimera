import random
import string

# ============================================================================
# SMT-LIB Keywords and Reserved Words
# ============================================================================

SMTLIB_KEYWORDS = {
    'true', 'false', 'not', 'and', 'or', 'xor', 'distinct', 'ite',
    'let', 'forall', 'exists', 'lambda', 'as', 'Bool', 'par',
    'assert', 'check-sat', 'declare-fun', 'declare-const', 'declare-sort',
    'define-fun', 'define-sort', 'get-model', 'get-value', 'push', 'pop',
    'set-logic', 'set-option', 'set-info', 'get-info', 'get-option',
    'exit', 'reset', 'echo', 'Int', 'Real', 'String', 'Array',
}

# ============================================================================
# Configuration
# ============================================================================

MAX_DEPTH = 5
MAX_ARITY = 4
MAX_VARS = 6
MAX_FUNCTIONS = 5
MAX_SORTS = 3

# ============================================================================
# Name Generation
# ============================================================================

def generate_name(prefix='', min_len=5):
    """Generate a random name with at least min_len characters."""
    while True:
        length = random.randint(min_len, min_len + 5)
        name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length - len(prefix)))
        if name not in SMTLIB_KEYWORDS and len(name) >= min_len:
            return name

# ============================================================================
# Sort Management
# ============================================================================

class SortManager:
    def __init__(self):
        self.base_sorts = ['Bool']
        self.custom_sorts = []
        self.function_sorts = []
        
    def generate_custom_sorts(self, count):
        for _ in range(count):
            name = generate_name('sort')
            self.custom_sorts.append(name)
    
    def get_random_base_sort(self):
        all_base = self.base_sorts + self.custom_sorts
        return random.choice(all_base)
    
    def generate_function_sort(self, depth=0):
        if depth > 2 or random.random() < 0.3:
            return self.get_random_base_sort()
        
        arity = random.randint(1, 3)
        args = [self.get_random_base_sort() for _ in range(arity)]
        ret = self.get_random_base_sort()
        return f"(-> {' '.join(args)} {ret})"
    
    def get_random_sort(self, allow_function=True):
        if allow_function and random.random() < 0.3:
            return self.generate_function_sort()
        return self.get_random_base_sort()
    
    def get_declarations(self):
        decls = []
        for sort in self.custom_sorts:
            decls.append(f"(declare-sort {sort} 0)")
        return decls

# ============================================================================
# Symbol Management
# ============================================================================

class SymbolManager:
    def __init__(self, sort_manager):
        self.sort_manager = sort_manager
        self.constants = {}
        self.functions = {}
        self.bound_vars = []
        
    def add_constant(self, name, sort):
        self.constants[name] = sort
    
    def add_function(self, name, arg_sorts, ret_sort):
        self.functions[name] = (arg_sorts, ret_sort)
    
    def generate_constants(self, count):
        for _ in range(count):
            name = generate_name('const')
            sort = self.sort_manager.get_random_base_sort()
            self.add_constant(name, sort)
    
    def generate_functions(self, count):
        for _ in range(count):
            name = generate_name('func')
            arity = random.randint(1, MAX_ARITY)
            arg_sorts = [self.sort_manager.get_random_base_sort() for _ in range(arity)]
            ret_sort = self.sort_manager.get_random_base_sort()
            self.add_function(name, arg_sorts, ret_sort)
    
    def get_bool_constants(self):
        return [name for name, sort in self.constants.items() if sort == 'Bool']
    
    def get_constants_of_sort(self, sort):
        return [name for name, s in self.constants.items() if s == sort]
    
    def push_scope(self, vars_dict):
        self.bound_vars.append(vars_dict)
    
    def pop_scope(self):
        if self.bound_vars:
            self.bound_vars.pop()
    
    def get_bound_vars_of_sort(self, sort):
        result = []
        for scope in self.bound_vars:
            for name, s in scope.items():
                if s == sort:
                    result.append(name)
        return result
    
    def get_declarations(self):
        decls = []
        for name, sort in self.constants.items():
            decls.append(f"(declare-const {name} {sort})")
        for name, (arg_sorts, ret_sort) in self.functions.items():
            args_str = ' '.join(arg_sorts)
            decls.append(f"(declare-fun {name} ({args_str}) {ret_sort})")
        return decls

# ============================================================================
# Term Generator
# ============================================================================

class TermGenerator:
    def __init__(self, sort_manager, symbol_manager):
        self.sort_manager = sort_manager
        self.symbol_manager = symbol_manager
    
    def generate_bool_term(self, depth=0):
        if depth >= MAX_DEPTH:
            return self._generate_bool_leaf()
        
        choices = [
            ('leaf', 0.2),
            ('not', 0.1),
            ('and', 0.15),
            ('or', 0.15),
            ('implies', 0.1),
            ('xor', 0.05),
            ('equals', 0.1),
            ('ite', 0.05),
            ('quantifier', 0.05),
            ('application', 0.05),
        ]
        
        choice = self._weighted_choice(choices)
        
        if choice == 'leaf':
            return self._generate_bool_leaf()
        elif choice == 'not':
            inner = self.generate_bool_term(depth + 1)
            return f"(not {inner})"
        elif choice == 'and':
            n = random.randint(2, 4)
            terms = [self.generate_bool_term(depth + 1) for _ in range(n)]
            return f"(and {' '.join(terms)})"
        elif choice == 'or':
            n = random.randint(2, 4)
            terms = [self.generate_bool_term(depth + 1) for _ in range(n)]
            return f"(or {' '.join(terms)})"
        elif choice == 'implies':
            n = random.randint(2, 3)
            terms = [self.generate_bool_term(depth + 1) for _ in range(n)]
            return f"(=> {' '.join(terms)})"
        elif choice == 'xor':
            n = random.randint(2, 3)
            terms = [self.generate_bool_term(depth + 1) for _ in range(n)]
            return f"(xor {' '.join(terms)})"
        elif choice == 'equals':
            sort = self.sort_manager.get_random_base_sort()
            n = random.randint(2, 3)
            terms = [self.generate_term_of_sort(sort, depth + 1) for _ in range(n)]
            return f"(= {' '.join(terms)})"
        elif choice == 'ite':
            cond = self.generate_bool_term(depth + 1)
            then_term = self.generate_bool_term(depth + 1)
            else_term = self.generate_bool_term(depth + 1)
            return f"(ite {cond} {then_term} {else_term})"
        elif choice == 'quantifier':
            return self._generate_quantifier(depth)
        elif choice == 'application':
            return self._generate_application_bool(depth)
        else:
            return self._generate_bool_leaf()
    
    def _generate_bool_leaf(self):
        choices = []
        
        choices.append(('true', 0.2))
        choices.append(('false', 0.2))
        
        bool_consts = self.symbol_manager.get_bool_constants()
        bound_bool_vars = self.symbol_manager.get_bound_vars_of_sort('Bool')
        
        if bool_consts:
            choices.append(('const', 0.3))
        if bound_bool_vars:
            choices.append(('bound', 0.3))
        
        choice = self._weighted_choice(choices)
        
        if choice == 'true':
            return 'true'
        elif choice == 'false':
            return 'false'
        elif choice == 'const' and bool_consts:
            return random.choice(bool_consts)
        elif choice == 'bound' and bound_bool_vars:
            return random.choice(bound_bool_vars)
        else:
            return random.choice(['true', 'false'])
    
    def generate_term_of_sort(self, sort, depth=0):
        if depth >= MAX_DEPTH:
            return self._generate_leaf_of_sort(sort)
        
        if sort == 'Bool':
            return self.generate_bool_term(depth)
        
        choices = [
            ('leaf', 0.5),
            ('ite', 0.2),
            ('application', 0.3),
        ]
        
        choice = self._weighted_choice(choices)
        
        if choice == 'leaf':
            return self._generate_leaf_of_sort(sort)
        elif choice == 'ite':
            cond = self.generate_bool_term(depth + 1)
            then_term = self.generate_term_of_sort(sort, depth + 1)
            else_term = self.generate_term_of_sort(sort, depth + 1)
            return f"(ite {cond} {then_term} {else_term})"
        elif choice == 'application':
            return self._generate_application_of_sort(sort, depth)
        else:
            return self._generate_leaf_of_sort(sort)
    
    def _generate_leaf_of_sort(self, sort):
        consts = self.symbol_manager.get_constants_of_sort(sort)
        bound = self.symbol_manager.get_bound_vars_of_sort(sort)
        
        candidates = consts + bound
        
        if candidates:
            return random.choice(candidates)
        
        # Generate a fresh constant
        name = generate_name('fresh')
        self.symbol_manager.add_constant(name, sort)
        return name
    
    def _generate_quantifier(self, depth):
        quantifier = random.choice(['forall', 'exists'])
        num_vars = random.randint(1, 3)
        
        var_bindings = {}
        sorted_vars = []
        
        for _ in range(num_vars):
            var_name = generate_name('qvar')
            var_sort = self.sort_manager.get_random_base_sort()
            var_bindings[var_name] = var_sort
            sorted_vars.append(f"({var_name} {var_sort})")
        
        self.symbol_manager.push_scope(var_bindings)
        body = self.generate_bool_term(depth + 1)
        self.symbol_manager.pop_scope()
        
        sorted_vars_str = ' '.join(sorted_vars)
        return f"({quantifier} ({sorted_vars_str}) {body})"
    
    def _generate_application_bool(self, depth):
        # Find functions that return Bool
        bool_funcs = [(name, args, ret) for name, (args, ret) in self.symbol_manager.functions.items() if ret == 'Bool']
        
        if not bool_funcs:
            return self._generate_bool_leaf()
        
        name, arg_sorts, ret_sort = random.choice(bool_funcs)
        args = [self.generate_term_of_sort(sort, depth + 1) for sort in arg_sorts]
        return f"({name} {' '.join(args)})"
    
    def _generate_application_of_sort(self, sort, depth):
        # Find functions that return the given sort
        funcs = [(name, args, ret) for name, (args, ret) in self.symbol_manager.functions.items() if ret == sort]
        
        if not funcs:
            return self._generate_leaf_of_sort(sort)
        
        name, arg_sorts, ret_sort = random.choice(funcs)
        args = [self.generate_term_of_sort(s, depth + 1) for s in arg_sorts]
        return f"({name} {' '.join(args)})"
    
    def _weighted_choice(self, choices):
        items = [item for item, weight in choices]
        weights = [weight for item, weight in choices]
        total = sum(weights)
        if total == 0:
            return random.choice(items)
        normalized = [w / total for w in weights]
        return random.choices(items, weights=normalized)[0]

# ============================================================================
# Main Generator Function
# ============================================================================

def generate_hocore_formula_with_decls():
    # Initialize managers
    sort_manager = SortManager()
    symbol_manager = SymbolManager(sort_manager)
    term_generator = TermGenerator(sort_manager, symbol_manager)
    
    # Generate sorts
    num_custom_sorts = random.randint(0, MAX_SORTS)
    sort_manager.generate_custom_sorts(num_custom_sorts)
    
    # Generate constants
    num_constants = random.randint(2, MAX_VARS)
    symbol_manager.generate_constants(num_constants)
    
    # Generate functions
    num_functions = random.randint(1, MAX_FUNCTIONS)
    symbol_manager.generate_functions(num_functions)
    
    # Generate formula
    formula = term_generator.generate_bool_term()
    
    # Collect declarations
    decls = []
    decls.extend(sort_manager.get_declarations())
    decls.extend(symbol_manager.get_declarations())
    
    decls_str = '\n'.join(decls)
    
    return decls_str, formula