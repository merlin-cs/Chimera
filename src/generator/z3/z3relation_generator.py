# complete Python module
import random
import string

# --- Constants ---

# A set of SMT-LIB keywords and common symbols to avoid as generated names.
SMT_KEYWORDS = {
    # SMT-LIB Standard v2.6 Commands
    "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec",
    "define-sort", "echo", "exit", "get-assertions", "get-assignment",
    "get-info", "get-model", "get-option", "get-proof", "get-unsat-core",
    "get-value", "pop", "push", "reset", "reset-assertions", "set-info",
    "set-logic", "set-option",
    # Core Theory Symbols
    "Bool", "true", "false", "not", "and", "or", "xor", "=>", "ite", "=",
    "distinct",
    # Ints/Reals Theory Symbols
    "Int", "Real", "to_real", "to_int", "is_int", "-", "+", "*", "/", "div",
    "mod", "rem", "abs", "<=", "<", ">=", ">",
    # Other common theories
    "Array", "select", "store", "BitVec", "concat", "extract", "bvnot",
    "bvand", "bvor", "bvneg", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl",
    "bvlshr", "bvult", "bvslt",
    # Z3 Relation Theory Keywords
    "partial-order", "linear-order", "tree-order", "piecewise-linear-order",
    "transitive-closure",
    # Other keywords
    "let", "forall", "exists", "as", "_",
}

# Configuration for the generator
MAX_DEPTH = 4
MIN_NAME_LENGTH = 5
MAX_NAME_LENGTH = 8
Z3_INDEXED_RELATION_OPS = [
    "partial-order",
    "linear-order",
    "tree-order",
    "piecewise-linear-order",
]

# --- Helper: Name Generation ---

def _generate_name(context, length=None):
    """Generates a new random name not in SMT_KEYWORDS or context.used_names."""
    if length is None:
        length = random.randint(MIN_NAME_LENGTH, MAX_NAME_LENGTH)
    while True:
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in context.used_names:
            context.used_names.add(name)
            return name

# --- Helper: Context Management ---

class GenerationContext:
    """Holds the state for a single formula generation run."""
    def __init__(self):
        self.used_names = set(SMT_KEYWORDS)
        self.decls = []
        self.sorts = {'Bool': 'predefined', 'Int': 'predefined'}
        # functions: name -> ([arg_sorts], ret_sort)
        self.functions = {}
        # producers: sort -> [func_name, ...] (for functions and constants)
        self.producers = {'Bool': [], 'Int': []}
        # Binary relations suitable for transitive closure: list of (name, sort)
        self.relations_for_tc = []
        # Tracks next available index for indexed relations: op -> next_index
        self.indexed_relation_indices = {op: 0 for op in Z3_INDEXED_RELATION_OPS}

    def add_sort(self, name):
        """Declares a new uninterpreted sort."""
        if name not in self.sorts:
            self.sorts[name] = 'uninterpreted'
            self.producers[name] = []
            self.decls.append(f"(declare-sort {name} 0)")

    def add_function(self, name, arg_sorts, ret_sort):
        """Declares a new function or constant."""
        if name not in self.functions:
            self.functions[name] = (arg_sorts, ret_sort)
            arg_str = " ".join(arg_sorts)
            if arg_sorts:
                self.decls.append(f"(declare-fun {name} ({arg_str}) {ret_sort})")
            else: # It's a constant
                self.decls.append(f"(declare-const {name} {ret_sort})")

            if ret_sort not in self.producers:
                self.producers[ret_sort] = []
            self.producers[ret_sort].append(name)

            # Check if it's a binary relation for transitive closure
            if ret_sort == 'Bool' and len(arg_sorts) == 2 and arg_sorts[0] == arg_sorts[1]:
                domain_sort = arg_sorts[0]
                if domain_sort != 'Bool': # TC on Bool is less interesting
                    self.relations_for_tc.append((name, domain_sort))

    def get_producers_for_sort(self, sort):
        """Returns a list of function/constant names that produce the given sort."""
        return self.producers.get(sort, [])

    def get_indexed_relation_id(self, op):
        """Gets the next available index for a given indexed relation operator."""
        index = self.indexed_relation_indices[op]
        self.indexed_relation_indices[op] += 1
        return index

# --- Helper: Term Generation ---

def _generate_term(context, sort, depth):
    """Dispatcher to generate a term of a specific sort."""
    if depth >= MAX_DEPTH:
        # At max depth, must generate a terminal (constant or variable)
        if sort == 'Int':
            return str(random.randint(-100, 100))
        if sort == 'Bool':
            return random.choice(['true', 'false'])

        producers = context.get_producers_for_sort(sort)
        constants = [p for p in producers if not context.functions[p][0]]
        if constants:
            return random.choice(constants)
        
        # Fallback: if no constants exist, we must break the rules slightly
        # and declare one on the fly. This is a safeguard.
        const_name = _generate_name(context)
        context.add_function(const_name, [], sort)
        return const_name

    if sort == 'Bool':
        return _generate_bool_term(context, depth)
    elif sort == 'Int':
        return _generate_int_term(context, depth)
    else: # Uninterpreted sort
        return _generate_uninterpreted_term(context, sort, depth)

def _generate_uninterpreted_term(context, sort, depth):
    """Generates a term of a given uninterpreted sort."""
    producers = context.get_producers_for_sort(sort)
    
    # Prefer complex terms (function calls, ite) if not too deep
    if depth < MAX_DEPTH - 1:
        options = []
        if any(context.functions[p][0] for p in producers):
            options.append('func')
        options.append('ite')

        if options and random.random() < 0.7:
            choice = random.choice(options)
            if choice == 'func':
                callable_producers = [p for p in producers if context.functions[p][0]]
                func_name = random.choice(callable_producers)
                arg_sorts, _ = context.functions[func_name]
                args = [_generate_term(context, s, depth + 1) for s in arg_sorts]
                return f"({func_name} {' '.join(args)})"
            else:  # 'ite'
                cond = _generate_term(context, 'Bool', depth + 1)
                arg1 = _generate_term(context, sort, depth + 1)
                arg2 = _generate_term(context, sort, depth + 1)
                return f"(ite {cond} {arg1} {arg2})"

    # Fallback to constant
    constants = [p for p in producers if not context.functions[p][0]]
    if constants:
        return random.choice(constants)
    
    # Safeguard: declare a constant if none exist
    const_name = _generate_name(context)
    context.add_function(const_name, [], sort)
    return const_name

def _generate_int_term(context, depth):
    """Generates a term of sort Int."""
    choices = ['const', 'producer']
    if depth < MAX_DEPTH - 1:
        choices.extend(['+', '-', '*', 'ite'])

    choice = random.choice(choices)

    if choice == 'const':
        return str(random.randint(-100, 100))
    
    if choice == 'producer':
        producers = context.get_producers_for_sort('Int')
        if producers:
            # Re-use the logic for generating function calls or ites
            return _generate_uninterpreted_term(context, 'Int', depth)
        else: # Fallback
            return str(random.randint(-100, 100))

    if choice == 'ite':
        cond = _generate_term(context, 'Bool', depth + 1)
        arg1 = _generate_term(context, 'Int', depth + 1)
        arg2 = _generate_term(context, 'Int', depth + 1)
        return f"(ite {cond} {arg1} {arg2})"

    if choice in ['+', '-', '*']:
        arg1 = _generate_term(context, 'Int', depth + 1)
        arg2 = _generate_term(context, 'Int', depth + 1)
        return f"({choice} {arg1} {arg2})"
    
    return str(random.randint(0, 10)) # Should not be reached

def _generate_z3_relation_application(context, depth):
    """Generates a Z3 relation application term."""
    use_tc = random.random() < 0.4 and context.relations_for_tc
    
    if use_tc:
        # Generate (_ transitive-closure R) term1 term2
        rel_name, sort = random.choice(context.relations_for_tc)
        arg1 = _generate_term(context, sort, depth + 1)
        arg2 = _generate_term(context, sort, depth + 1)
        return f"((_ transitive-closure {rel_name}) {arg1} {arg2})"
    else:
        # Generate (_ <op> index) term1 term2
        op = random.choice(Z3_INDEXED_RELATION_OPS)
        index = context.get_indexed_relation_id(op)
        
        # Pick a sort for the relation to operate on. These axiomatic relations
        # are defined over uninterpreted sorts.
        operable_sorts = [s for s, v in context.sorts.items() if v == 'uninterpreted']
        if not operable_sorts:
             # This should not happen if context is populated correctly.
             # If it does, we cannot generate this term. Fall back to a simple bool.
             return random.choice(['true', 'false'])
        sort = random.choice(operable_sorts)
        
        arg1 = _generate_term(context, sort, depth + 1)
        arg2 = _generate_term(context, sort, depth + 1)
        return f"((_ {op} {index}) {arg1} {arg2})"

def _generate_bool_term(context, depth):
    """Generates a term of sort Bool."""
    options = ['producer']
    if depth < MAX_DEPTH - 1:
        options.extend(['and', 'or', 'not', 'ite', '=', 'z3_rel', 'cmp'])

    # Weights to encourage diversity
    weights = {
        'producer': 10, 'and': 15, 'or': 15, 'not': 10, 'ite': 10,
        '=': 15, 'z3_rel': 5, 'cmp': 10
    }
    if not context.relations_for_tc and not any(v == 'uninterpreted' for v in context.sorts.values()):
        weights['z3_rel'] = 0

    # Filter out impossible options
    possible_options = [opt for opt in options if weights.get(opt, 0) > 0]
    if not possible_options: # Should only happen at max depth
        possible_options = ['producer']

    choice = random.choices(
        possible_options,
        weights=[weights[opt] for opt in possible_options],
        k=1
    )[0]

    if choice == 'producer':
        producers = context.get_producers_for_sort('Bool')
        if producers:
            return _generate_uninterpreted_term(context, 'Bool', depth)
        else: # Fallback to true/false
            return random.choice(['true', 'false'])

    if choice in ['and', 'or']:
        arg1 = _generate_term(context, 'Bool', depth + 1)
        arg2 = _generate_term(context, 'Bool', depth + 1)
        return f"({choice} {arg1} {arg2})"

    if choice == 'not':
        arg = _generate_term(context, 'Bool', depth + 1)
        return f"(not {arg})"

    if choice == 'ite':
        cond = _generate_term(context, 'Bool', depth + 1)
        # The result of this ite must be Bool, as we are in _generate_bool_term.
        arg1 = _generate_term(context, 'Bool', depth + 1)
        arg2 = _generate_term(context, 'Bool', depth + 1)
        return f"(ite {cond} {arg1} {arg2})"

    if choice == '=':
        # Pick a random sort to compare
        eq_sort = random.choice(list(context.sorts.keys()))
        arg1 = _generate_term(context, eq_sort, depth + 1)
        arg2 = _generate_term(context, eq_sort, depth + 1)
        return f"(= {arg1} {arg2})"
    
    if choice == 'cmp': # Integer comparisons
        op = random.choice(['<=', '<', '>=', '>'])
        arg1 = _generate_term(context, 'Int', depth + 1)
        arg2 = _generate_term(context, 'Int', depth + 1)
        return f"({op} {arg1} {arg2})"

    if choice == 'z3_rel':
        return _generate_z3_relation_application(context, depth)

    # Fallback
    return random.choice(['true', 'false'])

# --- Helper: Context Population ---

def _populate_context(context):
    """Fills the context with a random set of sorts, functions, and constants."""
    # 1. Create uninterpreted sorts
    num_sorts = random.randint(1, 2)
    for _ in range(num_sorts):
        sort_name = _generate_name(context)
        context.add_sort(sort_name)

    available_sorts = list(context.sorts.keys())

    # 2. Create constants for each sort
    for sort in available_sorts:
        num_consts = random.randint(1, 3)
        for _ in range(num_consts):
            const_name = _generate_name(context)
            context.add_function(const_name, [], sort)

    # 3. Create functions
    num_funcs = random.randint(2, 5)
    for _ in range(num_funcs):
        func_name = _generate_name(context)
        arity = random.randint(1, 3)
        arg_sorts = random.choices(available_sorts, k=arity)
        ret_sort = random.choice(available_sorts)
        context.add_function(func_name, arg_sorts, ret_sort)

    # 4. Ensure at least one binary relation exists for Transitive Closure
    if not context.relations_for_tc:
        uninterp_sorts = [s for s, v in context.sorts.items() if v == 'uninterpreted']
        if not uninterp_sorts: # If we only have Bool/Int, use Int
            target_sort = 'Int'
        else:
            target_sort = random.choice(uninterp_sorts)

        rel_name = _generate_name(context)
        context.add_function(rel_name, [target_sort, target_sort], 'Bool')

# --- Public Function ---

def generate_z3relation_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula using z3_relation theory.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): SMT-LIB2 declarations for all symbols used.
        - formula (str): A single SMT-LIB2 Boolean term.
    """
    context = GenerationContext()
    _populate_context(context)
    
    formula_str = _generate_bool_term(context, 0)
    
    # Filter out any empty lines that might have been added
    decls_list = [d for d in context.decls if d]
    decls_str = "\n".join(decls_list)
    
    return decls_str, formula_str