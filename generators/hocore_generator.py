# complete Python module
import random
import string

# --- Configuration ---
MAX_DEPTH = 5
MAX_ARGS = 4  # For n-ary operators and functions
MAX_QUANT_VARS = 3 # For forall/exists/lambda

_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "exists", "forall",
    "lambda", "let", "assert", "check-sat", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-sort", "exit", "get-assertions",
    "get-assignment", "get-info", "get-model", "get-option", "get-proof",
    "get-unsat-core", "get-value", "pop", "push", "set-info", "set-logic",
    "set-option", "Bool", "Int", "Real", "String", "Array", "_", "as",
    "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "par", "!", "@"
}

# --- Helper for Symbol Naming ---

def _generate_name(used_names, length_min=5, length_max=8):
    """Generates a random, valid, and unused SMT-LIB symbol name."""
    while True:
        length = random.randint(length_min, length_max)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in used_names and name not in _SMT_KEYWORDS:
            used_names.add(name)
            return name

# --- Sort Representation and Formatting ---

# A Sort is represented as either:
# 1. A string for a simple sort (e.g., "Bool", "mysort").
# 2. A tuple ('->', [arg_sorts], ret_sort) for a function sort.

def _format_sort(sort):
    """Converts the internal sort representation to an SMT-LIB string."""
    if isinstance(sort, str):
        return sort
    elif isinstance(sort, tuple) and sort[0] == '->':
        _, arg_sorts, ret_sort = sort
        formatted_args = " ".join(_format_sort(s) for s in arg_sorts)
        return f"(-> {formatted_args} {_format_sort(ret_sort)})"
    raise TypeError(f"Invalid sort representation: {sort}")


# --- Generation Context ---

class Context:
    """Manages state during formula generation."""
    def __init__(self):
        self.used_names = set()
        self.declarations = []
        
        # Simple sorts are just strings of their names
        self.simple_sorts = {"Bool"}
        
        # Scopes for variables (lambda, forall, exists)
        # Each scope is a dict[str, Sort]
        self.scopes = []
        
        # Global symbols (functions, constants)
        # dict[str, Sort]
        self.global_symbols = {}

    def add_declaration(self, decl_str):
        self.declarations.append(decl_str)

    def add_simple_sort(self):
        name = _generate_name(self.used_names)
        self.simple_sorts.add(name)
        self.add_declaration(f"(declare-sort {name} 0)")
        return name

    def add_global_symbol(self, sort):
        name = _generate_name(self.used_names)
        
        if isinstance(sort, str): # Constant
            self.global_symbols[name] = sort
            self.add_declaration(f"(declare-const {name} {_format_sort(sort)})")
        elif isinstance(sort, tuple) and sort[0] == '->': # Function
            _, arg_sorts, ret_sort = sort
            self.global_symbols[name] = sort
            formatted_args = " ".join(_format_sort(s) for s in arg_sorts)
            self.add_declaration(f"(declare-fun {name} ({formatted_args}) {_format_sort(ret_sort)})")
        return name

    def push_scope(self, new_vars):
        """new_vars is a dict[str, Sort]"""
        self.scopes.append(new_vars)

    def pop_scope(self):
        self.scopes.pop()

    def find_symbols_of_sort(self, target_sort):
        """Finds all visible symbols (local and global) of a given sort."""
        matches = []
        # Search local scopes from innermost to outermost
        for scope in reversed(self.scopes):
            for name, sort in scope.items():
                if sort == target_sort:
                    matches.append(name)
        # Search global symbols
        for name, sort in self.global_symbols.items():
            if sort == target_sort:
                matches.append(name)
        return matches

# --- Recursive Generation Functions ---

def _generate_sort(ctx, depth):
    """Generates a random sort (simple or functional)."""
    # Base case: at max depth, must be a simple sort
    if depth <= 0 or random.random() < 0.6:
        return random.choice(list(ctx.simple_sorts))

    # Recursive case: generate a function sort
    num_args = random.randint(1, MAX_ARGS - 1)
    arg_sorts = [_generate_sort(ctx, depth - 1) for _ in range(num_args)]
    ret_sort = _generate_sort(ctx, depth - 1)
    return ('->', arg_sorts, ret_sort)

def _generate_term(ctx, target_sort, depth):
    """Generates a random term of a given sort. Corresponds to <term>."""
    if target_sort == "Bool":
        return _generate_boolean_term(ctx, depth)

    # --- Terminal case: depth limit reached ---
    if depth <= 0:
        # Must produce a variable or constant of the target sort
        candidates = ctx.find_symbols_of_sort(target_sort)
        if candidates:
            return random.choice(candidates)
        # Fallback: if no symbol exists, we must create one.
        return ctx.add_global_symbol(target_sort)

    # --- Recursive cases for non-boolean terms ---
    productions = []
    weights = []

    # Production 1: A variable or constant of the target sort
    candidates = ctx.find_symbols_of_sort(target_sort)
    if candidates:
        productions.append("symbol")
        weights.append(10)

    # Production 2: An application that results in the target sort
    app_candidates = []
    all_symbols = {**ctx.global_symbols}
    for scope in ctx.scopes:
        all_symbols.update(scope)
        
    for name, sort in all_symbols.items():
        if isinstance(sort, tuple) and sort[0] == '->':
            _, _, ret_sort = sort
            if ret_sort == target_sort:
                app_candidates.append((name, sort))
    if app_candidates:
        productions.append("application")
        weights.append(20)

    # Production 3: An `ite` expression
    productions.append("ite")
    weights.append(15)
    
    # Production 4: A `lambda` expression (if target is a function sort)
    if isinstance(target_sort, tuple) and target_sort[0] == '->':
        productions.append("lambda")
        weights.append(15)

    if not productions:
        # Failsafe: if no other option, create a new global constant
        return ctx.add_global_symbol(target_sort)

    choice = random.choices(productions, weights=weights, k=1)[0]

    if choice == "symbol":
        return random.choice(candidates)
    
    if choice == "ite":
        cond = _generate_boolean_term(ctx, depth - 1)
        then_branch = _generate_term(ctx, target_sort, depth - 1)
        else_branch = _generate_term(ctx, target_sort, depth - 1)
        return f"(ite {cond} {then_branch} {else_branch})"

    if choice == "lambda":
        _, arg_sorts, ret_sort = target_sort
        
        bound_vars = {}
        var_decls = []
        for arg_sort in arg_sorts:
            var_name = _generate_name(ctx.used_names)
            bound_vars[var_name] = arg_sort
            var_decls.append(f"({var_name} {_format_sort(arg_sort)})")
        
        ctx.push_scope(bound_vars)
        body = _generate_term(ctx, ret_sort, depth - 1)
        ctx.pop_scope()
        
        return f"(lambda ({' '.join(var_decls)}) {body})"

    if choice == "application":
        func_name, func_sort = random.choice(app_candidates)
        _, arg_sorts, _ = func_sort
        
        args = [_generate_term(ctx, s, depth - 1) for s in arg_sorts]
        
        if len(args) == 1 and random.random() < 0.2:
             return f"(@ {func_name} {args[0]})"
        return f"({func_name} {' '.join(args)})"
        
    return ctx.add_global_symbol(target_sort)


def _generate_boolean_term(ctx, depth):
    """Generates a random boolean term. Corresponds to <boolean_term>."""
    if depth <= 0:
        candidates = ctx.find_symbols_of_sort("Bool")
        if candidates:
            return random.choice(candidates)
        return random.choice(["true", "false"])

    productions = ["true", "false"]
    weights = [2, 2]

    bool_symbols = ctx.find_symbols_of_sort("Bool")
    if bool_symbols:
        productions.append("symbol")
        weights.append(10)

    productions.extend(["not", "and", "or", "xor", "=>"])
    weights.extend([10, 15, 15, 10, 10])

    productions.extend(["=", "ite"])
    weights.extend([15, 10])

    productions.extend(["forall", "exists"])
    weights.extend([8, 8])
    
    app_candidates = []
    all_symbols = {**ctx.global_symbols}
    for scope in ctx.scopes:
        all_symbols.update(scope)
    for name, sort in all_symbols.items():
        if isinstance(sort, tuple) and sort[0] == '->' and sort[2] == 'Bool':
            app_candidates.append((name, sort))
    if app_candidates:
        productions.append("application")
        weights.append(15)

    choice = random.choices(productions, weights=weights, k=1)[0]

    if choice == "true": return "true"
    if choice == "false": return "false"
    if choice == "symbol": return random.choice(bool_symbols)

    if choice == "not":
        sub_term = _generate_boolean_term(ctx, depth - 1)
        return f"(not {sub_term})"

    if choice in {"and", "or", "xor", "=>"}:
        num_args = random.randint(2, MAX_ARGS)
        args = [_generate_boolean_term(ctx, depth - 1) for _ in range(num_args)]
        return f"({choice} {' '.join(args)})"

    if choice == "ite":
        cond = _generate_boolean_term(ctx, depth - 1)
        then_b = _generate_boolean_term(ctx, depth - 1)
        else_b = _generate_boolean_term(ctx, depth - 1)
        return f"(ite {cond} {then_b} {else_b})"

    if choice == "=":
        comp_sort = _generate_sort(ctx, depth - 1)
        term1 = _generate_term(ctx, comp_sort, depth - 1)
        term2 = _generate_term(ctx, comp_sort, depth - 1)
        return f"(= {term1} {term2})"

    if choice in {"forall", "exists"}:
        num_vars = random.randint(1, MAX_QUANT_VARS)
        bound_vars = {}
        var_decls = []
        for _ in range(num_vars):
            var_sort = _generate_sort(ctx, depth - 1)
            var_name = _generate_name(ctx.used_names)
            bound_vars[var_name] = var_sort
            var_decls.append(f"({var_name} {_format_sort(var_sort)})")
        
        ctx.push_scope(bound_vars)
        body = _generate_boolean_term(ctx, depth - 1)
        ctx.pop_scope()
        
        return f"({choice} ({' '.join(var_decls)}) {body})"

    if choice == "application":
        func_name, func_sort = random.choice(app_candidates)
        _, arg_sorts, _ = func_sort
        args = [_generate_term(ctx, s, depth - 1) for s in arg_sorts]
        
        if len(args) == 1 and random.random() < 0.2:
             return f"(@ {func_name} {args[0]})"
        return f"({func_name} {' '.join(args)})"

    return "true"


# --- Public API ---

def generate_hocore_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula for the HO-Core logic.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): SMT-LIB2 declarations for all symbols.
        - formula (str): A single SMT-LIB2 Boolean term.
    """
    ctx = Context()

    # 1. Initialize context with some base sorts and symbols
    num_base_sorts = random.randint(1, 3)
    for _ in range(num_base_sorts):
        ctx.add_simple_sort()

    num_base_symbols = random.randint(2, 5)
    for _ in range(num_base_symbols):
        sort = _generate_sort(ctx, depth=2)
        ctx.add_global_symbol(sort)
        
    # Ensure at least one constant for each simple sort exists for terminal cases
    for s_sort in ctx.simple_sorts:
        if not ctx.find_symbols_of_sort(s_sort):
            ctx.add_global_symbol(s_sort)

    # 2. Generate the main boolean formula
    formula_str = _generate_boolean_term(ctx, depth=MAX_DEPTH)

    # 3. Format declarations
    decls_str = "\n".join(ctx.declarations)

    return decls_str, formula_str