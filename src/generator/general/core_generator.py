# complete Python module
import random
import string

# A set of SMT-LIB 2 keywords to avoid for generated names. This helps prevent
# syntax errors in the generated output.
_SMT_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', '=>', 'xor', '=', 'distinct',
    'assert', 'check-sat', 'declare-const', 'declare-fun', 'declare-sort',
    'define-fun', 'define-sort', 'exit', 'get-assertions', 'get-assignment',
    'get-info', 'get-model', 'get-option', 'get-proof', 'get-unsat-core',
    'get-value', 'pop', 'push', 'set-info', 'set-logic', 'set-option',
    'Int', 'Real', 'Bool', 'Array', 'forall', 'exists', 'let', 'par'
}


class _FormulaGenerator:
    """
    A stateful class to manage the generation of a single random SMT-LIB formula.
    This class is a private implementation detail and is not intended for public use.
    It follows the provided CFG to construct a well-typed Boolean term.
    """
    def __init__(self):
        # --- Configuration ---
        self.MAX_DEPTH = random.randint(4, 7)
        self.MAX_NARY_ARITY = 5
        self.MIN_NAME_LEN = 5
        self.MAX_NAME_LEN = 8
        self.N_ARY_BOOL_OPS = ['=>', 'and', 'or', 'xor']

        # --- Generation State ---
        self.used_names = set(_SMT_KEYWORDS)
        self.sorts = ['Bool']
        self.funcs = {}  # str -> (list[str], str)  (name -> ([arg_sorts], ret_sort))
        self.vars = {}   # str -> str              (name -> sort)

    def _generate_unique_name(self):
        """Generates a random, unique name that is not an SMT-LIB keyword."""
        while True:
            length = random.randint(self.MIN_NAME_LEN, self.MAX_NAME_LEN)
            name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _initialize_declarations(self):
        """Populates the generator's state with random sorts, functions, and variables."""
        # 1. Declare custom sorts
        num_sorts = random.randint(1, 3)
        for _ in range(num_sorts):
            sort_name = self._generate_unique_name()
            self.sorts.append(sort_name)

        # 2. Declare variables/constants, ensuring at least one per sort exists.
        # This guarantees that the base case of term generation never fails.
        for sort in self.sorts:
            var_name = self._generate_unique_name()
            self.vars[var_name] = sort
        
        num_extra_vars = random.randint(5, 15)
        for _ in range(num_extra_vars):
            var_name = self._generate_unique_name()
            var_sort = random.choice(self.sorts)
            self.vars[var_name] = var_sort

        # 3. Declare functions (can have 0 arity, which makes them constants).
        num_funcs = random.randint(3, 8)
        for _ in range(num_funcs):
            func_name = self._generate_unique_name()
            arity = random.randint(0, 4)
            arg_sorts = random.choices(self.sorts, k=arity)
            ret_sort = random.choice(self.sorts)
            self.funcs[func_name] = (arg_sorts, ret_sort)

    def _get_vars_of_sort(self, sort):
        """Returns a list of declared variable names of a given sort."""
        return [name for name, s in self.vars.items() if s == sort]

    def _get_funcs_returning_sort(self, sort):
        """Returns a list of (name, signature) for functions returning a given sort."""
        return [
            (name, sig) for name, sig in self.funcs.items() if sig[1] == sort
        ]

    def _generate_term(self, depth, sort):
        """
        Generates a term of a specific sort, corresponding to the <term> CFG rule.
        <term> ::= <bool_term> | <symbol> | '(' <symbol> <term>* ')'
        """
        if sort == 'Bool':
            # A <bool_term> is a valid <term> of sort Bool.
            return self._generate_bool_term(depth)

        # Find possible generators for the given non-Boolean sort
        possible_vars = self._get_vars_of_sort(sort)
        possible_funcs = self._get_funcs_returning_sort(sort)

        # At max depth, must use a variable (which is guaranteed to exist).
        # Also use a variable if no functions can produce this sort.
        if depth >= self.MAX_DEPTH or not possible_funcs:
            return random.choice(possible_vars)

        # Recursive case: choose between a variable or a function application.
        # Bias towards function applications to create more nested terms.
        use_func = random.choices([True, False], weights=[0.75, 0.25], k=1)[0]

        if use_func:
            func_name, (arg_sorts, _) = random.choice(possible_funcs)
            if not arg_sorts: # 0-arity function (constant)
                return func_name
            
            args = [self._generate_term(depth + 1, s) for s in arg_sorts]
            return f"({func_name} {' '.join(args)})"
        else:
            return random.choice(possible_vars)

    def _generate_bool_term(self, depth):
        """
        Generates a boolean term, corresponding to the <bool_term> CFG rule.
        """
        bool_vars = self._get_vars_of_sort('Bool')
        
        # At max depth, can only generate terminals (variables or literals).
        if depth >= self.MAX_DEPTH:
            return random.choice(bool_vars + ['true', 'false'])

        # Define all possible productions and their weights for random selection.
        # Weights are chosen to promote diversity in generated formulas.
        productions = [
            'symbol', 'literal', 'not', 'n_ary_op', 'ite', 'equals', 'distinct'
        ]
        weights = [10, 5, 15, 20, 15, 15, 20]
        
        choice = random.choices(productions, weights=weights, k=1)[0]

        if choice == 'symbol':
            return random.choice(bool_vars)
        
        elif choice == 'literal':
            return random.choice(['true', 'false'])

        elif choice == 'not':
            arg = self._generate_bool_term(depth + 1)
            return f"(not {arg})"

        elif choice == 'n_ary_op':
            op = random.choice(self.N_ARY_BOOL_OPS)
            arity = random.randint(2, self.MAX_NARY_ARITY)
            args = [self._generate_bool_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"

        elif choice == 'ite':
            cond = self._generate_bool_term(depth + 1)
            then_b = self._generate_bool_term(depth + 1)
            else_b = self._generate_bool_term(depth + 1)
            return f"(ite {cond} {then_b} {else_b})"

        elif choice == 'equals' or choice == 'distinct':
            op = '=' if choice == 'equals' else 'distinct'
            arity = random.randint(2, self.MAX_NARY_ARITY)
            # Pick a random sort for the arguments of '=' or 'distinct'.
            arg_sort = random.choice(self.sorts)
            args = [self._generate_term(depth + 1, arg_sort) for _ in range(arity)]
            return f"({op} {' '.join(args)})"
        
        # Fallback case, should not be reached due to exhaustive choices.
        return 'true'

    def generate(self):
        """
        The main generation driver. Initializes declarations, generates the formula,
        and formats the declarations and formula into strings.
        """
        self._initialize_declarations()
        
        formula_str = self._generate_bool_term(0)

        decls = []
        # Sort declarations
        for sort_name in sorted(self.sorts):
            if sort_name != 'Bool':
                decls.append(f"(declare-sort {sort_name} 0)")
        
        # Variable/Constant declarations
        for var_name, var_sort in sorted(self.vars.items()):
            decls.append(f"(declare-const {var_name} {var_sort})")
            
        # Function declarations
        for func_name, (arg_sorts, ret_sort) in sorted(self.funcs.items()):
            arg_str = ' '.join(arg_sorts)
            decls.append(f"(declare-fun {func_name} ({arg_str}) {ret_sort})")
        
        decls_str = "\n".join(decls)
        
        return decls_str, formula_str


def generate_core_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB formula for the Core theory.

    This function implements a generator based on a context-free grammar for
    Boolean terms in the Core theory. It randomizes the structure, operators,
    and number of variables/functions to create diverse formulas suitable for
    testing or fuzzing SMT solvers.

    Every symbol used in the formula is declared with the correct sort and arity.
    The generation process is constrained by a random depth limit to ensure
    termination and produce formulas of reasonable size.

    Returns:
        tuple[str, str]: A tuple containing:
            - A string of SMT-LIB declarations for all generated symbols.
            - A string representing the generated Boolean term.
    """
    generator = _FormulaGenerator()
    return generator.generate()