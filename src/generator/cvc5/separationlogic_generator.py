# complete Python module
import random
import string

# SMT-LIB 2 keywords to avoid for generated names.
_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "=", "ite", "true", "false", "sep", "wand",
    "pto", "sep.emp", "declare-sort", "declare-fun", "define-fun", "assert",
    "check-sat", "get-model", "exit", "set-logic", "declare-const", "push",
    "pop", "get-value", "let", "forall", "exists", "match", "par", "as", "_",
    "NUMERAL", "DECIMAL", "HEXADECIMAL", "BINARY", "STRING", "continued-execution",
    "error", "immediate-exit", "incomplete", "logic", "memout", "sat",
    "success", "theory", "unknown", "unsupported", "unsat",
    # Core theory keywords that might be used as sort names
    "Int", "Bool", "Real", "String", "Array", "select", "store"
}

# Configuration for the generator
_MAX_DEPTH = 5
_MAX_ARITY = 4


class _SeparationLogicGenerator:
    """
    Manages state and generation logic for a single random formula.
    This class is not intended for public use and encapsulates the entire
    generation process for one call.
    """
    def __init__(self):
        self.used_names = set(_SMT_KEYWORDS)
        self.decls = []
        self.sorts = {"Bool", "Int"}
        self.symbols = {"Bool": ["true", "false"], "Int": []}
        self.functions = {}  # {return_sort: [(name, [arg_sorts...]), ...]}
        self.loc_sort = ""
        self.data_sort = ""

    def _generate_name(self, length_min=5, length_max=8):
        """Generates a new, unique, random lowercase ASCII name."""
        while True:
            length = random.randint(length_min, length_max)
            name = "".join(random.choice(string.ascii_lowercase) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _add_symbol(self, sort, name):
        """Adds a symbol of a given sort to the state's symbol table."""
        if sort not in self.symbols:
            self.symbols[sort] = []
        self.symbols[sort].append(name)

    def _add_function(self, name, arg_sorts, return_sort):
        """Adds a function signature to the state's function table."""
        if return_sort not in self.functions:
            self.functions[return_sort] = []
        self.functions[return_sort].append((name, arg_sorts))

    def _declare_sort(self, name):
        """Adds a sort declaration to the list of declarations."""
        self.sorts.add(name)
        self.decls.append(f"(declare-sort {name} 0)")

    def _declare_const(self, name, sort):
        """Adds a constant (0-arity function) declaration."""
        self.decls.append(f"(declare-const {name} {sort})")
        self._add_symbol(sort, name)

    def _declare_fun(self, name, arg_sorts, return_sort):
        """Adds a function declaration."""
        args_str = " ".join(arg_sorts)
        self.decls.append(f"(declare-fun {name} ({args_str}) {return_sort})")
        self._add_function(name, arg_sorts, return_sort)

    def _initialize_state(self):
        """
        Sets up the initial environment by declaring necessary sorts,
        constants, and functions before formula generation begins.
        """
        # Declare mandatory Separation Logic sorts
        self.loc_sort = self._generate_name()
        self.data_sort = self._generate_name()
        self._declare_sort(self.loc_sort)
        self._declare_sort(self.data_sort)

        # Optionally declare a few extra uninterpreted sorts for variety
        for _ in range(random.randint(0, 2)):
            self._declare_sort(self._generate_name())
        
        all_sorts = list(self.sorts)

        # Declare some constants/variables for each available sort
        for sort in all_sorts:
            for _ in range(random.randint(2, 4)):
                self._declare_const(self._generate_name(), sort)

        # Add some integer literals to the symbol table
        for _ in range(5):
            self._add_symbol("Int", str(random.randint(-100, 100)))

        # Declare some random background functions and predicates
        for _ in range(random.randint(1, 3)): # Predicates (return Bool)
            arity = random.randint(1, 3)
            arg_sorts = random.choices(all_sorts, k=arity)
            self._declare_fun(self._generate_name(), arg_sorts, "Bool")
        
        non_bool_sorts = [s for s in all_sorts if s != "Bool"]
        if non_bool_sorts: # Other functions (return non-Bool)
            for _ in range(random.randint(1, 3)):
                arity = random.randint(1, 3)
                arg_sorts = random.choices(all_sorts, k=arity)
                return_sort = random.choice(non_bool_sorts)
                self._declare_fun(self._generate_name(), arg_sorts, return_sort)

        # Add standard Int operators to the function table (not declared)
        for op in ["+", "-", "*"]:
            self._add_function(op, ["Int", "Int"], "Int")
        for op in ["<", "<=", ">", ">=", "="]:
            self._add_function(op, ["Int", "Int"], "Bool")
        
        # Add equality for SL and other custom sorts
        for sort in self.sorts - {"Int", "Bool"}:
            self._add_function("=", [sort, sort], "Bool")

    def _generate_term(self, target_sort, depth):
        """
        Implements the <term> rule from the CFG for a specific sort.
        Generates a constant, literal, or function application of the target sort.
        """
        can_recur = depth < _MAX_DEPTH and self.functions.get(target_sort)
        
        if not can_recur: # Base case: must be a symbol/literal
            if target_sort in self.symbols and self.symbols[target_sort]:
                return random.choice(self.symbols[target_sort])
            else: # Safeguard: declare a new const if no symbols exist
                const_name = self._generate_name()
                self._declare_const(const_name, target_sort)
                return const_name

        # Recursive case: choose between a symbol or a function application
        choice = random.choices(["symbol", "function"], weights=[30, 70], k=1)[0]

        if choice == "symbol":
            return random.choice(self.symbols[target_sort])
        else: # function
            fun_name, arg_sorts = random.choice(self.functions[target_sort])
            args = [self._generate_term(s, depth + 1) for s in arg_sorts]
            return f"({fun_name} {' '.join(args)})"

    def _generate_background_bool_term(self, depth):
        """Implements the <background_bool_term> rule."""
        if depth >= _MAX_DEPTH:
            return random.choice(self.symbols["Bool"])
        
        bool_funcs = self.functions.get("Bool", [])
        options = ["symbol"]
        if bool_funcs:
            options.append("function")
        
        choice = random.choices(options, weights=[40, 60], k=1)[0]

        if choice == "symbol":
            bool_vars = [s for s in self.symbols["Bool"] if s not in ["true", "false"]]
            return random.choice(bool_vars) if bool_vars else random.choice(["true", "false"])
        else: # function
            fun_name, arg_sorts = random.choice(bool_funcs)
            args = [self._generate_term(s, depth + 1) for s in arg_sorts]
            return f"({fun_name} {' '.join(args)})"

    def _generate_sl_atomic_formula(self, depth):
        """Implements the <sl_atomic_formula> rule."""
        options = ["sep.emp", "pto", "background"]
        weights = [10, 45, 45]
        choice = random.choices(options, weights=weights, k=1)[0]
        
        if choice == "sep.emp":
            return "sep.emp"
        elif choice == "pto":
            loc_term = self._generate_term(self.loc_sort, depth + 1)
            data_term = self._generate_term(self.data_sort, depth + 1)
            return f"(pto {loc_term} {data_term})"
        else: # background
            return self._generate_background_bool_term(depth + 1)

    def _generate_sl_bool_term(self, depth):
        """Implements the <sl_bool_term> (start symbol) rule recursively."""
        if depth >= _MAX_DEPTH:
            return self._generate_sl_atomic_formula(depth)

        rules = ["atomic", "sep", "wand", "boolean_op", "ite", "not"]
        weights = [20, 15, 15, 20, 15, 15] # Biased for diversity
        chosen_rule = random.choices(rules, weights=weights, k=1)[0]

        if chosen_rule == "atomic":
            return self._generate_sl_atomic_formula(depth + 1)
        
        elif chosen_rule == "not":
            arg = self._generate_sl_bool_term(depth + 1)
            return f"(not {arg})"

        elif chosen_rule == "ite":
            parts = [self._generate_sl_bool_term(depth + 1) for _ in range(3)]
            return f"(ite {parts[0]} {parts[1]} {parts[2]})"

        elif chosen_rule == "wand":
            arg1 = self._generate_sl_bool_term(depth + 1)
            arg2 = self._generate_sl_bool_term(depth + 1)
            return f"(wand {arg1} {arg2})"
        
        elif chosen_rule == "sep":
            op = "sep"
            # The CFG says 1+, but semantically it's often used with 2+ arguments.
            # Generating 2+ makes for more interesting separating conjunctions.
            arity = random.randint(2, _MAX_ARITY)
            args = [self._generate_sl_bool_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"

        else: # boolean_op
            op = random.choice(['and', 'or', 'xor', '=>', '='])
            # The CFG says 1+, but most ops are semantically binary or more.
            # We generate 2+ to create more typical SMT formulas.
            arity = random.randint(2, _MAX_ARITY)
            args = [self._generate_sl_bool_term(depth + 1) for _ in range(arity)]
            return f"({op} {' '.join(args)})"

    def run(self):
        """Main entry point to generate a formula."""
        self._initialize_state()
        formula = self._generate_sl_bool_term(depth=0)
        return "\n".join(self.decls), formula


def generate_separationlogic_formula_with_decls():
    """
    Generates a random, well-formed SMT-LIB2 formula for the Separation_Logic
    theory, along with all necessary declarations.

    This function implements a generator based on a CFG for Separation Logic
    terms, prioritizing structural diversity and compliance with SMT-LIB2 syntax.
    It uses only the Python standard library.

    Returns:
        tuple[str, str]: A tuple containing:
            - A string of SMT-LIB2 declarations for all sorts and symbols used.
            - A string representing the generated Boolean term.
    """
    generator = _SeparationLogicGenerator()
    decls_str, formula_str = generator.run()
    return decls_str, formula_str