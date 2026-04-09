# complete Python module
import random
import string

# SMT-LIB keywords to avoid for generated symbol names.
_SMT_KEYWORDS = {
    "abs", "and", "assert", "as", "Array", "check-sat", "check-sat-assuming",
    "declare-const", "declare-fun", "declare-sort", "define-fun", "define-sort",
    "distinct", "div", "echo", "exists", "exit", "false", "forall",
    "get-assertions", "get-assignment", "get-info", "get-model", "get-option",
    "get-proof", "get-unsat-core", "get-value", "if", "Int", "ite", "lambda",
    "let", "mod", "not", "or", "pop", "push", "reset", "set-info", "set-logic",
    "set-option", "String", "true", "xor", "Bool", "Unicode",
    "=>", "=", ">", ">=", "<", "<=", "+", "-", "*", "/",
    "seq.++", "seq.at", "seq.contains", "seq.extract", "seq.in_re",
    "seq.indexof", "seq.is_digit", "seq.len", "seq.lt", "seq.le", "seq.map",
    "seq.nth", "seq.prefixof", "seq.replace", "seq.suffixof", "seq.to_re",
    "seq.unit", "str.to_int", "int.to_str", "re.all", "re.allchar", "re.comp",
    "re.diff", "re.inter", "re.loop", "re.opt", "re.plus", "re.range",
    "re.star", "re.union", "seq.empty", "seq.fold_left", "seq.foldl",
    "seq.fold_lefti", "seq.foldli", "seq.mapi"
}

# --- Configuration for the generator ---
_MAX_DEPTH = 5
_MAX_BREADTH = 3 # For variadic operators like 'and', '+'
_MIN_NAME_LEN = 5
_MAX_NAME_LEN = 8


class _FormulaGenerator:
    """
    Encapsulates the state and logic for generating a single random formula.
    This class directly implements the logic derived from the provided CFG.
    """

    def __init__(self):
        self.declarations = []
        self.used_names = set(_SMT_KEYWORDS)
        
        # Data structures to track sorts and symbols
        self.sorts = {}  # name -> structure, e.g., 'MySeq': ('Seq', 'Int')
        self.symbols = {} # name -> sort
        self.functions = {} # name -> ([arg_sorts], ret_sort)
        
        # Randomize generation parameters for this run
        self.max_depth = random.randint(3, _MAX_DEPTH)
        self.max_breadth = random.randint(2, _MAX_BREADTH)

    def _sort_to_str(self, sort):
        """Converts internal sort representation to an SMT-LIB string."""
        if isinstance(sort, tuple):
            return f"({' '.join(self._sort_to_str(s) for s in sort)})"
        return sort

    def _generate_name(self):
        """Generates a new, unique, random symbol name."""
        while True:
            length = random.randint(_MIN_NAME_LEN, _MAX_NAME_LEN)
            name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _get_symbols_of_sort(self, sort):
        """Returns a list of all declared symbols matching a given sort."""
        return [name for name, s in self.symbols.items() if s == sort]

    def _get_functions_of_signature(self, arg_sorts, ret_sort):
        """Returns functions matching a given signature."""
        return [
            name for name, sig in self.functions.items() 
            if sig == (arg_sorts, ret_sort)
        ]

    def _declare_sort(self, name, definition=None):
        """Declares a new sort."""
        self.sorts[name] = definition if definition is not None else name
        if definition is None: # Uninterpreted sort
            self.declarations.append(f"(declare-sort {name} 0)")

    def _declare_symbol(self, sort):
        """Declares a new constant/variable of a given sort."""
        name = self._generate_name()
        self.symbols[name] = sort
        self.declarations.append(f"(declare-const {name} {self._sort_to_str(sort)})")
        return name
        
    def _declare_function(self, arg_sorts, ret_sort):
        """Declares a new uninterpreted function."""
        name = self._generate_name()
        self.functions[name] = (tuple(arg_sorts), ret_sort)
        arg_strs = ' '.join(self._sort_to_str(s) for s in arg_sorts)
        ret_str = self._sort_to_str(ret_sort)
        self.declarations.append(f"(declare-fun {name} ({arg_strs}) {ret_str})")
        return name

    def _setup_initial_context(self):
        """Populates the context with basic and random sorts, symbols, and functions."""
        # Base sorts
        self.sorts['Bool'] = 'Bool'
        self.sorts['Int'] = 'Int'
        self.sorts['Unicode'] = 'Unicode'
        self.sorts['String'] = ('Seq', 'Unicode')

        # Create some random uninterpreted sorts
        for _ in range(random.randint(0, 2)):
            self._declare_sort(self._generate_name())
        
        available_sorts = list(self.sorts.values())
        
        # Create some sequence sorts from existing sorts
        for _ in range(random.randint(1, 3)):
            element_sort = random.choice(available_sorts)
            if element_sort == 'Bool': continue # (Seq Bool) is not standard
            seq_sort_name = self._generate_name()
            self._declare_sort(seq_sort_name, ('Seq', element_sort))
        
        available_sorts = list(self.sorts.values())

        # Declare some symbols for each sort
        for sort in available_sorts:
            for _ in range(random.randint(1, 3)):
                self._declare_symbol(sort)

        # Declare some functions
        for _ in range(random.randint(1, 4)):
            num_args = random.randint(1, 3)
            arg_sorts = tuple(random.choice(available_sorts) for _ in range(num_args))
            ret_sort = random.choice(available_sorts)
            self._declare_function(arg_sorts, ret_sort)
    
    # --- TERMINAL GENERATORS ---

    def _gen_bool_literal(self, depth, sort):
        return random.choice(["true", "false"]), 'Bool'

    def _gen_int_literal(self, depth, sort):
        return str(random.randint(-100, 100)), 'Int'

    def _gen_string_literal(self, depth, sort):
        length = random.randint(0, 10)
        content = "".join(random.choice(string.ascii_letters + string.digits + " ") for _ in range(length))
        # Escape quotes
        content = content.replace('"', '""')
        return f'"{content}"', self.sorts['String']

    def _gen_symbol(self, depth, sort):
        """Generates a variable/constant of a given sort."""
        candidates = self._get_symbols_of_sort(sort)
        if not candidates:
            # On-the-fly declaration if no suitable symbol exists
            return self._declare_symbol(sort), sort
        return random.choice(candidates), sort

    # --- TERM GENERATORS ---

    def _generate_term(self, depth, sort):
        """Dispatcher to generate a term of a specific sort."""
        if sort == 'Bool':
            return self._generate_bool_term(depth)
        if sort == 'Int':
            return self._generate_int_term(depth)
        if isinstance(sort, tuple):
            if sort[0] == 'Seq':
                return self._generate_seq_term(depth, sort)
            if sort[0] == 'Array':
                domain_sorts = sort[1:-1]
                range_sort = sort[-1]
                return self._generate_array_term(depth, domain_sorts, range_sort)
        
        # For uninterpreted sorts, we can only use symbols or functions/ites
        # that return this sort.
        gens = [(self._gen_symbol_of_sort, 50)]
        if depth > 0:
            gens.extend([(self._gen_function_call, 25), (self._gen_ite, 15)])
        
        # Add seq.nth if applicable
        seq_candidates = [(name, s_sort) for name, s_sort in self.symbols.items() 
                          if isinstance(s_sort, tuple) and s_sort[0] == 'Seq' and s_sort[1] == sort]
        if seq_candidates and depth > 0:
            gens.append((self._gen_seq_nth, 10))

        population = [g[0] for g in gens]
        weights = [g[1] for g in gens]
        chosen_gen = random.choices(population, weights, k=1)[0]
        return chosen_gen(depth, sort)
    
    def _generate_bool_term(self, depth):
        gens = [(self._gen_bool_literal, 10)]
        
        if depth <= 0:
            gens.append((self._gen_symbol_of_sort, 90))
        else:
            gens.extend([
                (self._gen_symbol_of_sort, 10), (self._gen_eq, 15),
                (self._gen_distinct, 5), (self._gen_not, 10),
                (self._gen_bool_connective, 20), (self._gen_int_comparison, 15),
                (self._gen_seq_bool_op, 15), (self._gen_ite, 5),
                (self._gen_function_call, 5),
            ])
        
        population = [g[0] for g in gens]
        weights = [g[1] for g in gens]
        chosen_gen = random.choices(population, weights, k=1)[0]
        return chosen_gen(depth, 'Bool')

    def _generate_int_term(self, depth):
        gens = [(self._gen_int_literal, 20)]
        if depth <= 0:
            gens.append((self._gen_symbol_of_sort, 80))
        else:
            gens.extend([
                (self._gen_symbol_of_sort, 20), (self._gen_arith_op, 30),
                (self._gen_unary_minus, 5), (self._gen_seq_len, 10),
                (self._gen_seq_indexof, 10), (self._gen_ite, 5),
                (self._gen_function_call, 5),
            ])

        population = [g[0] for g in gens]
        weights = [g[1] for g in gens]
        chosen_gen = random.choices(population, weights, k=1)[0]
        return chosen_gen(depth, 'Int')

    def _generate_seq_term(self, depth, sort):
        gens = []
        if sort == self.sorts['String']:
            gens.append((self._gen_string_literal, 20))
        
        if depth <= 0:
            gens.append((self._gen_symbol_of_sort, 80))
        else:
            gens.extend([
                (self._gen_symbol_of_sort, 20), (self._gen_seq_unit, 10),
                (self._gen_seq_empty, 5), (self._gen_seq_concat, 20),
                (self._gen_seq_extract, 10), (self._gen_seq_at, 5),
                (self._gen_seq_replace, 10), (self._gen_seq_map, 5),
                (self._gen_ite, 5), (self._gen_function_call, 5),
            ])

        population = [g[0] for g in gens]
        weights = [g[1] for g in gens]
        if not population:
            return self._gen_symbol(depth, sort)

        chosen_gen = random.choices(population, weights, k=1)[0]
        return chosen_gen(depth, sort)
    
    def _generate_array_term(self, depth, domain_sorts, range_sort):
        """Generates a lambda or a function symbol."""
        array_sort = ('Array', *domain_sorts, range_sort)
        candidates = self._get_symbols_of_sort(array_sort)
        
        use_symbol = candidates and random.choice([True, False])
        if use_symbol:
            return random.choice(candidates), array_sort
        
        # Generate a lambda
        arg_names = [self._generate_name() for _ in domain_sorts]
        
        original_symbols = self.symbols.copy()
        for name, sort in zip(arg_names, domain_sorts):
            self.symbols[name] = sort
            
        body, _ = self._generate_term(depth - 1, range_sort)
        
        self.symbols = original_symbols
        
        sorted_vars = ' '.join(f"({name} {self._sort_to_str(sort)})" for name, sort in zip(arg_names, domain_sorts))
        return f"(lambda ({sorted_vars}) {body})", array_sort

    # --- SPECIFIC PRODUCTION GENERATORS ---

    def _gen_symbol_of_sort(self, depth, sort):
        return self._gen_symbol(depth, sort)

    def _gen_eq(self, depth, sort):
        eq_sort = random.choice(list(self.sorts.values()))
        t1, _ = self._generate_term(depth - 1, eq_sort)
        t2, _ = self._generate_term(depth - 1, eq_sort)
        return f"(= {t1} {t2})", 'Bool'

    def _gen_distinct(self, depth, sort):
        dist_sort = random.choice(list(self.sorts.values()))
        num_args = random.randint(2, self.max_breadth)
        args = [self._generate_term(depth - 1, dist_sort)[0] for _ in range(num_args)]
        return f"(distinct {' '.join(args)})", 'Bool'

    def _gen_not(self, depth, sort):
        arg, _ = self._generate_bool_term(depth - 1)
        return f"(not {arg})", 'Bool'

    def _gen_bool_connective(self, depth, sort):
        op = random.choice(["and", "or", "=>", "xor"])
        num_args = random.randint(2, self.max_breadth)
        args = [self._generate_bool_term(depth - 1)[0] for _ in range(num_args)]
        return f"({op} {' '.join(args)})", 'Bool'

    def _gen_int_comparison(self, depth, sort):
        op = random.choice(["<", "<=", ">", ">="])
        t1, _ = self._generate_int_term(depth - 1)
        t2, _ = self._generate_int_term(depth - 1)
        return f"({op} {t1} {t2})", 'Bool'

    def _gen_seq_bool_op(self, depth, sort):
        seq_sorts = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Seq']
        if not seq_sorts: return self._gen_bool_literal(depth, sort)
        
        target_seq_sort = random.choice(seq_sorts)
        op = random.choice(["seq.contains", "seq.prefixof", "seq.suffixof"])
        
        s1, _ = self._generate_seq_term(depth - 1, target_seq_sort)
        s2, _ = self._generate_seq_term(depth - 1, target_seq_sort)
        return f"({op} {s1} {s2})", 'Bool'

    def _gen_ite(self, depth, sort):
        cond, _ = self._generate_bool_term(depth - 1)
        t1, _ = self._generate_term(depth - 1, sort)
        t2, _ = self._generate_term(depth - 1, sort)
        return f"(ite {cond} {t1} {t2})", sort

    def _gen_function_call(self, depth, sort):
        # Includes fold operations as they return a generic term
        fold_op = None
        if random.random() < 0.2: # small chance to generate a fold
            fold_op = random.choice(["seq.fold_left", "seq.fold_lefti"])

        if fold_op:
            all_seq_sorts = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Seq']
            if not all_seq_sorts: return self._gen_symbol(depth, sort)
            
            s_sort = random.choice(all_seq_sorts)
            t_sort = s_sort[1] # element sort
            u_sort = sort # accumulator/return sort

            s, _ = self._generate_seq_term(depth - 1, s_sort)
            a, _ = self._generate_term(depth - 1, u_sort)

            if fold_op == "seq.fold_left":
                f, _ = self._generate_array_term(depth-1, [u_sort, t_sort], u_sort)
                return f"({fold_op} {f} {a} {s})", u_sort
            else: # seq.fold_lefti
                f, _ = self._generate_array_term(depth-1, ['Int', u_sort, t_sort], u_sort)
                i, _ = self._generate_int_term(depth-1)
                return f"({fold_op} {f} {i} {a} {s})", u_sort

        # Regular uninterpreted function call
        candidates = [(name, sig) for name, sig in self.functions.items() if sig[1] == sort]
        if not candidates: return self._gen_symbol(depth, sort)
        
        name, (arg_sorts, ret_sort) = random.choice(candidates)
        args = [self._generate_term(depth - 1, s)[0] for s in arg_sorts]
        return f"({name} {' '.join(args)})", ret_sort

    def _gen_arith_op(self, depth, sort):
        op = random.choice(["+", "*", "div", "mod"])
        # SMT-LIB `-` can be n-ary, but unary is handled separately
        if random.random() > 0.5:
            op = "-"
        num_args = random.randint(2, self.max_breadth)
        args = [self._generate_int_term(depth - 1)[0] for _ in range(num_args)]
        return f"({op} {' '.join(args)})", 'Int'

    def _gen_unary_minus(self, depth, sort):
        arg, _ = self._generate_int_term(depth - 1)
        return f"(- {arg})", 'Int'
    
    def _gen_seq_len(self, depth, sort):
        seq_sorts = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Seq']
        if not seq_sorts: return self._gen_int_literal(depth, sort)
        
        target_seq_sort = random.choice(seq_sorts)
        s, _ = self._generate_seq_term(depth - 1, target_seq_sort)
        return f"(seq.len {s})", 'Int'

    def _gen_seq_indexof(self, depth, sort):
        seq_sorts = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Seq']
        if not seq_sorts: return self._gen_int_literal(depth, sort)
        
        target_seq_sort = random.choice(seq_sorts)
        s1, _ = self._generate_seq_term(depth - 1, target_seq_sort)
        s2, _ = self._generate_seq_term(depth - 1, target_seq_sort)
        
        if random.choice([True, False]):
            offset, _ = self._generate_int_term(depth - 1)
            return f"(seq.indexof {s1} {s2} {offset})", 'Int'
        else:
            return f"(seq.indexof {s1} {s2})", 'Int'

    def _gen_seq_unit(self, depth, sort):
        element_sort = sort[1]
        element, _ = self._generate_term(depth - 1, element_sort)
        return f"(seq.unit {element})", sort
        
    def _gen_seq_empty(self, depth, sort):
        return f"(as seq.empty {self._sort_to_str(sort)})", sort

    def _gen_seq_concat(self, depth, sort):
        num_args = random.randint(2, self.max_breadth)
        args = [self._generate_seq_term(depth - 1, sort)[0] for _ in range(num_args)]
        return f"(seq.++ {' '.join(args)})", sort

    def _gen_seq_extract(self, depth, sort):
        s, _ = self._generate_seq_term(depth - 1, sort)
        i, _ = self._generate_int_term(depth - 1)
        j, _ = self._generate_int_term(depth - 1)
        return f"(seq.extract {s} {i} {j})", sort

    def _gen_seq_at(self, depth, sort):
        s, _ = self._generate_seq_term(depth - 1, sort)
        i, _ = self._generate_int_term(depth - 1)
        return f"(seq.at {s} {i})", sort

    def _gen_seq_replace(self, depth, sort):
        s1, _ = self._generate_seq_term(depth - 1, sort)
        s2, _ = self._generate_seq_term(depth - 1, sort)
        s3, _ = self._generate_seq_term(depth - 1, sort)
        return f"(seq.replace {s1} {s2} {s3})", sort
    
    def _gen_seq_nth(self, depth, sort):
        # Find a sequence `s` of sort `(Seq sort)`
        seq_candidates = [(name, s_sort) for name, s_sort in self.symbols.items() 
                          if isinstance(s_sort, tuple) and s_sort[0] == 'Seq' and s_sort[1] == sort]
        if not seq_candidates:
            return self._gen_symbol(depth, sort)

        seq_name, _ = random.choice(seq_candidates)
        idx, _ = self._generate_int_term(depth - 1)
        return f"(seq.nth {seq_name} {idx})", sort

    def _gen_seq_map(self, depth, sort):
        # Result is `sort`=(Seq U). Input `s`=(Seq T). Map `f`=(Array T U).
        all_seq_sorts = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Seq']
        if not all_seq_sorts: return self._gen_symbol(depth, sort)
        
        source_seq_sort = random.choice(all_seq_sorts)
        t_sort = source_seq_sort[1]
        u_sort = sort[1]
        
        s, _ = self._generate_seq_term(depth - 1, source_seq_sort)
        
        op = random.choice(["seq.map", "seq.mapi"])
        if op == "seq.map":
             f, _ = self._generate_array_term(depth - 1, (t_sort,), u_sort)
             return f"(seq.map {f} {s})", sort
        else: # seq.mapi
             f_mapi, _ = self._generate_array_term(depth - 1, ('Int', t_sort), u_sort)
             i, _ = self._generate_int_term(depth-1)
             return f"(seq.mapi {f_mapi} {i} {s})", sort

    def generate(self):
        """Main generation orchestrator."""
        self._setup_initial_context()
        
        # The start symbol of the CFG is <bool_term>
        formula_str, _ = self._generate_bool_term(self.max_depth)
        
        decls_str = "\n".join(self.declarations)
        
        return decls_str, formula_str


def generate_z3seq_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula using z3_seq theory.

    This function implements a generator based on a detailed CFG for SMT-LIB
    Boolean terms involving sequences, integers, and uninterpreted functions.
    It prioritizes structural diversity and type correctness.

    Returns:
        tuple[str, str]: A tuple containing:
            - A string of SMT-LIB2 declarations for all used sorts, constants,
              and functions.
            - A string representing the generated Boolean term (the formula).
    """
    generator = _FormulaGenerator()
    return generator.generate()