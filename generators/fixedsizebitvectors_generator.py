# complete Python module
import random
import string

# SMT-LIB keywords to avoid for symbol names.
_SMT_KEYWORDS = {
    "!", "_", "as", "assert", "check-sat", "check-sat-assuming", "declare-const",
    "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort",
    "define-fun", "define-fun-rec", "define-funs-rec", "define-sort", "echo",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core",
    "get-value", "pop", "push", "reset", "reset-assertions", "set-info",
    "set-logic", "set-option", "and", "or", "not", "xor", "=>", "ite", "true",
    "false", "let", "forall", "exists", "distinct", "bvult", "bvnego", "bvuaddo",
    "bvsaddo", "bvumulo", "bvsmulo", "concat", "extract", "bvnot", "bvneg",
    "bvand", "bvor", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl", "bvlshr",
    "int_to_bv", "ubv_to_int", "sbv_to_int", "Bool", "Int", "BitVec",
    "+", "-", "*", "div", "mod",
}

class _FormulaGenerator:
    """
    A stateful class to generate a single, random, well-typed SMT-LIB formula
    for the FixedSizeBitVectors theory, following a given CFG.
    """

    def __init__(self):
        # --- Configuration ---
        self.max_depth = 5
        self.max_let_bindings = 3
        self.max_quant_vars = 3
        self.max_n_ary_args = 4
        self.bv_widths = [1, 4, 8, 16, 32, 64]
        self.initial_consts_per_sort = 2

        # --- Generation State ---
        self.used_names = set(_SMT_KEYWORDS)
        self.declarations = []
        # For global constants/functions declared with declare-const/declare-fun
        self.consts_by_sort = {}  # sort_str -> [name, ...]
        # For variables bound by let/quantifiers
        self.scoped_vars = []  # A stack of scopes: [ {name: sort}, ... ]

    def generate(self):
        """Main entry point to generate a formula."""
        self._pre_declare_consts()
        formula_str, _ = self._generate_bool_term(0)
        return "\n".join(self.declarations), formula_str

    # --- Symbol and Sort Helpers ---

    def _generate_symbol_name(self):
        """Generates a new, unique, valid symbol name."""
        while True:
            length = random.randint(5, 10)
            name = "".join(random.choice(string.ascii_lowercase) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _get_random_bv_sort(self):
        """Returns a random BitVec sort string."""
        width = random.choice(self.bv_widths)
        return f"(_ BitVec {width})"

    def _get_random_sort(self):
        """Returns a random sort string from Bool, Int, or BitVec."""
        return random.choice(["Bool", "Int", self._get_random_bv_sort()])

    def _get_width_from_sort(self, bv_sort_str):
        """Extracts the width from a '(_ BitVec width)' string."""
        return int(bv_sort_str.split(" ")[2][:-1])

    def _declare_const(self, sort):
        """Declares a new constant of a given sort and returns its name."""
        name = self._generate_symbol_name()
        self.declarations.append(f"(declare-const {name} {sort})")
        if sort not in self.consts_by_sort:
            self.consts_by_sort[sort] = []
        self.consts_by_sort[sort].append(name)
        return name

    def _pre_declare_consts(self):
        """Creates an initial set of constants for basic sorts."""
        for _ in range(self.initial_consts_per_sort):
            self._declare_const("Bool")
            self._declare_const("Int")
            self._declare_const(self._get_random_bv_sort())
        # Ensure at least one of each width exists
        for width in self.bv_widths:
            sort = f"(_ BitVec {width})"
            if sort not in self.consts_by_sort:
                 self._declare_const(sort)


    def _get_symbol_of_sort(self, sort):
        """
        Finds an existing scoped variable or global constant of a given sort.
        If none exist, creates a new global constant.
        """
        available = []
        # Look in scoped variables first (innermost scope to outermost)
        for scope in reversed(self.scoped_vars):
            for name, s in scope.items():
                if s == sort:
                    available.append(name)
        
        # Look in global constants
        if sort in self.consts_by_sort:
            available.extend(self.consts_by_sort[sort])

        if available and random.random() < 0.8:  # 80% chance to reuse
            return random.choice(available)
        
        # Otherwise, declare a new global constant
        return self._declare_const(sort)

    # --- Literal Generation ---

    def _generate_bv_literal(self, width):
        """Generates a #b or #x literal of a given width."""
        # Hex literals have a width that is 4 * num_digits.
        # To ensure the literal has the correct width, we only generate
        # hex literals if the width is a multiple of 4.
        if width % 4 == 0 and random.random() < 0.5:  # Hex
            hex_len = width // 4
            val = random.getrandbits(width)
            return f"#x{val:0{hex_len}x}"
        else:  # Binary
            return f"#b{''.join(random.choice('01') for _ in range(width))}"

    def _generate_numeral(self):
        """Generates a non-negative integer literal string."""
        return str(random.randint(0, 1000))

    # --- Term Generation Dispatcher ---

    def _generate_term(self, depth, required_sort=None):
        """
        Dispatches to a specific term generator based on the required sort.
        Returns (term_string, sort_string).
        """
        if required_sort is None:
            sort_type = random.choices(["Bool", "Int", "BV"], weights=[3, 2, 5], k=1)[0]
            if sort_type == "Bool":
                return self._generate_bool_term(depth)
            elif sort_type == "Int":
                return self._generate_int_term(depth)
            else: # BV
                return self._generate_bv_term(depth, required_sort=None)
        
        if required_sort == "Bool":
            return self._generate_bool_term(depth)
        elif required_sort == "Int":
            return self._generate_int_term(depth)
        else: # Is a BV sort
            return self._generate_bv_term(depth, required_sort=required_sort)

    # --- Boolean Term Generation (<bool_term>) ---

    def _generate_bool_term(self, depth):
        """Generates a term of sort Bool."""
        is_max_depth = depth >= self.max_depth
        
        # At max depth, must produce a terminal (literal or variable).
        if is_max_depth:
            prod_choices = ["literal", "symbol"]
            prod_weights = [20, 80]
        else:
            prod_choices = ["literal", "symbol", "eq", "distinct", "not", "n_ary", "ite", "let", "quant", "bv_pred"]
            # Decrease weight of recursive structures with depth
            rec_weight = max(1, 15 - depth * 3)
            let_quant_weight = max(1, 5 - depth)
            prod_weights = [5, 10, rec_weight, rec_weight, rec_weight, rec_weight, rec_weight, let_quant_weight, let_quant_weight, rec_weight]

        choice = random.choices(prod_choices, weights=prod_weights, k=1)[0]

        if choice == "literal":
            return (random.choice(["true", "false"]), "Bool")
        
        if choice == "symbol":
            return (self._get_symbol_of_sort("Bool"), "Bool")

        if choice == "not":
            arg, _ = self._generate_bool_term(depth + 1)
            return (f"(not {arg})", "Bool")

        if choice == "n_ary":
            op = random.choice(["and", "or", "xor", "=>"])
            if op == "=>":
                num_args = 2
            else:
                num_args = random.randint(2, self.max_n_ary_args)
            args = [self._generate_bool_term(depth + 1)[0] for _ in range(num_args)]
            return (f"({op} {' '.join(args)})", "Bool")

        if choice == "eq" or choice == "distinct":
            op = "=" if choice == "eq" else "distinct"
            num_args = random.randint(2, self.max_n_ary_args)
            arg_sort = self._get_random_sort()
            args = [self._generate_term(depth + 1, required_sort=arg_sort)[0] for _ in range(num_args)]
            return (f"({op} {' '.join(args)})", "Bool")

        if choice == "ite":
            cond, _ = self._generate_bool_term(depth + 1)
            # Since this is _generate_bool_term, the ite must return a Bool.
            then_b, _ = self._generate_bool_term(depth + 1)
            else_b, _ = self._generate_bool_term(depth + 1)
            return (f"(ite {cond} {then_b} {else_b})", "Bool")

        if choice == "let":
            num_bindings = random.randint(1, self.max_let_bindings)
            bindings_str = []
            new_scope = {}
            for _ in range(num_bindings):
                var_name = self._generate_symbol_name()
                bound_term, bound_sort = self._generate_term(depth + 1)
                bindings_str.append(f"({var_name} {bound_term})")
                new_scope[var_name] = bound_sort
            
            self.scoped_vars.append(new_scope)
            # The body of the let must be boolean for the whole term to be boolean
            body, _ = self._generate_bool_term(depth + 1)
            self.scoped_vars.pop()
            
            return (f"(let ({' '.join(bindings_str)}) {body})", "Bool")

        if choice == "quant":
            op = random.choice(["forall", "exists"])
            num_vars = random.randint(1, self.max_quant_vars)
            sorted_vars_str = []
            new_scope = {}
            for _ in range(num_vars):
                var_name = self._generate_symbol_name()
                var_sort = self._get_random_sort()
                sorted_vars_str.append(f"({var_name} {var_sort})")
                new_scope[var_name] = var_sort
            
            self.scoped_vars.append(new_scope)
            # The body of a quantifier must be boolean
            body, _ = self._generate_bool_term(depth + 1)
            self.scoped_vars.pop()

            return (f"({op} ({' '.join(sorted_vars_str)}) {body})", "Bool")

        if choice == "bv_pred":
            # All are binary predicates that return Bool
            op = random.choice(["bvult", "bvuaddo", "bvsaddo", "bvumulo", "bvsmulo"])
            bv_sort = self._get_random_bv_sort()
            arg1, _ = self._generate_bv_term(depth + 1, required_sort=bv_sort)
            arg2, _ = self._generate_bv_term(depth + 1, required_sort=bv_sort)
            return (f"({op} {arg1} {arg2})", "Bool")
        
        # Fallback
        return ("true", "Bool")

    # --- Bit-Vector Term Generation (<bv_term>) ---

    def _generate_bv_term(self, depth, required_sort=None):
        """
        Generates a term of a BitVec sort.
        If required_sort is None, a random BV sort is chosen.
        """
        can_use_sizing_ops = False
        if required_sort is None:
            sort = self._get_random_bv_sort()
            # For unconstrained generation, any operator is fine
            can_use_sizing_ops = True
        else:
            sort = required_sort

        width = self._get_width_from_sort(sort)
        is_max_depth = depth >= self.max_depth

        if is_max_depth:
            prod_choices = ["literal", "symbol"]
            prod_weights = [40, 60]
        else:
            prod_choices = ["literal", "symbol", "ite", "let", "unary", "n_ary", "binary", "int_to_bv"]
            prod_weights = [10, 15, 10, 5, 15, 15, 15, 5]
            if can_use_sizing_ops:
                prod_choices.extend(["concat", "extract"])
                prod_weights.extend([10, 10])

        choice = random.choices(prod_choices, weights=prod_weights, k=1)[0]

        if choice == "literal":
            return (self._generate_bv_literal(width), sort)
        
        if choice == "symbol":
            return (self._get_symbol_of_sort(sort), sort)

        if choice == "ite":
            cond, _ = self._generate_bool_term(depth + 1)
            then_b, _ = self._generate_bv_term(depth + 1, required_sort=sort)
            else_b, _ = self._generate_bv_term(depth + 1, required_sort=sort)
            return (f"(ite {cond} {then_b} {else_b})", sort)

        if choice == "let":
            num_bindings = random.randint(1, self.max_let_bindings)
            bindings_str = []
            new_scope = {}
            for _ in range(num_bindings):
                var_name = self._generate_symbol_name()
                bound_term, bound_sort = self._generate_term(depth + 1)
                bindings_str.append(f"({var_name} {bound_term})")
                new_scope[var_name] = bound_sort
            
            self.scoped_vars.append(new_scope)
            body, _ = self._generate_bv_term(depth + 1, required_sort=sort)
            self.scoped_vars.pop()
            
            return (f"(let ({' '.join(bindings_str)}) {body})", sort)

        if choice == "unary":
            op = random.choice(["bvnot", "bvneg"])
            arg, _ = self._generate_bv_term(depth + 1, required_sort=sort)
            return (f"({op} {arg})", sort)

        if choice in ["n_ary", "binary"]:
            if choice == "n_ary":
                op = random.choice(["bvand", "bvor", "bvadd", "bvmul"])
                num_args = random.randint(2, self.max_n_ary_args)
            else: # binary
                op = random.choice(["bvudiv", "bvurem", "bvshl", "bvlshr"])
                num_args = 2
            args = [self._generate_bv_term(depth + 1, required_sort=sort)[0] for _ in range(num_args)]
            return (f"({op} {' '.join(args)})", sort)

        if choice == "int_to_bv":
            # This is an indexed op: ((_ int_to_bv width) <int_term>)
            arg, _ = self._generate_int_term(depth + 1)
            return (f"((_ int_to_bv {width}) {arg})", sort)

        if choice == "concat" and can_use_sizing_ops:
            possible_w1s = [w for w in self.bv_widths if w < width and (width - w) in self.bv_widths]
            if possible_w1s:
                w1 = random.choice(possible_w1s)
                w2 = width - w1
                arg1_sort = f"(_ BitVec {w1})"
                arg2_sort = f"(_ BitVec {w2})"
                arg1_str, _ = self._generate_bv_term(depth + 1, required_sort=arg1_sort)
                arg2_str, _ = self._generate_bv_term(depth + 1, required_sort=arg2_sort)
                return (f"(concat {arg1_str} {arg2_str})", sort)

        if choice == "extract" and can_use_sizing_ops:
            possible_src_widths = [w for w in self.bv_widths if w > width]
            if possible_src_widths:
                src_width = random.choice(possible_src_widths)
                src_sort = f"(_ BitVec {src_width})"
                arg, _ = self._generate_bv_term(depth + 1, required_sort=src_sort)
                j = random.randint(0, src_width - width)
                i = j + width - 1
                return (f"((_ extract {i} {j}) {arg})", sort)

        # Fallback
        return (self._generate_bv_literal(width), sort)

    # --- Integer Term Generation (<int_term>) ---

    def _generate_int_term(self, depth):
        """Generates a term of sort Int."""
        is_max_depth = depth >= self.max_depth

        if is_max_depth:
            prod_choices = ["literal", "symbol"]
            prod_weights = [40, 60]
        else:
            prod_choices = ["literal", "neg_literal", "symbol", "ite", "let", "from_bv", "n_ary", "binary"]
            rec_weight = max(1, 15 - depth * 3)
            prod_weights = [10, 5, 15, rec_weight, 5, rec_weight, rec_weight, rec_weight]

        choice = random.choices(prod_choices, weights=prod_weights, k=1)[0]

        if choice == "literal":
            return (self._generate_numeral(), "Int")
        
        if choice == "neg_literal":
            num = self._generate_numeral()
            # (- 0) is valid but just "0" is cleaner.
            return (f"(- {num})" if num != "0" else "0", "Int")

        if choice == "symbol":
            return (self._get_symbol_of_sort("Int"), "Int")

        if choice == "ite":
            cond, _ = self._generate_bool_term(depth + 1)
            then_b, _ = self._generate_int_term(depth + 1)
            else_b, _ = self._generate_int_term(depth + 1)
            return (f"(ite {cond} {then_b} {else_b})", "Int")

        if choice == "let":
            num_bindings = random.randint(1, self.max_let_bindings)
            bindings_str = []
            new_scope = {}
            for _ in range(num_bindings):
                var_name = self._generate_symbol_name()
                bound_term, bound_sort = self._generate_term(depth + 1)
                bindings_str.append(f"({var_name} {bound_term})")
                new_scope[var_name] = bound_sort
            
            self.scoped_vars.append(new_scope)
            body, _ = self._generate_int_term(depth + 1)
            self.scoped_vars.pop()
            
            return (f"(let ({' '.join(bindings_str)}) {body})", "Int")

        if choice == "from_bv":
            op = random.choice(["ubv_to_int", "sbv_to_int"])
            # Generate a bv_term of any sort
            arg, _ = self._generate_bv_term(depth + 1)
            return (f"({op} {arg})", "Int")

        if choice in ["n_ary", "binary"]:
            if choice == "n_ary":
                op = random.choice(["+", "*"])
                num_args = random.randint(2, self.max_n_ary_args)
            else: # binary
                op = random.choice(["-", "div", "mod"])
                # SMT-LIB allows n-ary subtraction
                num_args = random.randint(2, self.max_n_ary_args) if op == "-" else 2
            args = [self._generate_int_term(depth + 1)[0] for _ in range(num_args)]
            return (f"({op} {' '.join(args)})", "Int")
        
        # Fallback
        return (self._generate_numeral(), "Int")


def generate_fixedsizebitvectors_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB formula for the FixedSizeBitVectors
    theory, along with all necessary declarations.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): SMT-LIB2 declarations for all symbols used.
        - formula (str): A single SMT-LIB2 Boolean term.
    """
    generator = _FormulaGenerator()
    decls, formula = generator.generate()
    return decls, formula