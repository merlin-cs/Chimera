# complete Python module
import random
import string

# A comprehensive set of SMT-LIB keywords and reserved words to avoid in names.
SMT_KEYWORDS = {
    "abs", "and", "as", "assert", "assert-soft", "bag", "check-sat",
    "check-sat-assuming", "declare-const", "declare-fun", "declare-sort",
    "define-fun", "define-fun-rec", "define-funs-rec", "define-sort",
    "distinct", "error", "exit", "exists", "false", "forall", "get-assertions",
    "get-assignment", "get-info", "get-model", "get-option", "get-proof",
    "get-unsat-assumptions", "get-unsat-core", "get-value", "implies", "ite",
    "let", "not", "or", "pop", "push", "reset", "reset-assertions",
    "set-info", "set-logic", "set-option", "true", "xor", "par", "NUMERAL",
    "DECIMAL", "STRING", "declare-datatype", "declare-datatypes", "define",
    "define-const", "define-sort", "get-labels", "labels", "minimize",
    "maximize", "check-synth", "declare-var", "define-var", "simplify",
    "synth-fun", "synth-inv", "declare-stream", "define-stream",
    # Theory specific keywords
    "bag.member", "bag.subbag", "bag.empty", "bag.union_disjoint",
    "bag.union_max", "bag.inter_min", "bag.difference_subtract",
    "bag.difference_remove", "bag.setof", "bag.count",
    # Core theory keywords
    "=>", "=", "+", "-", "*", "/", "div", "mod", "<", "<=", ">", ">="
}

class _FormulaGenerator:
    """
    Internal class to manage state and generation logic for a single formula.
    This class directly implements the recursive generation based on the CFG.
    """
    def __init__(self):
        self.declarations = []
        self.used_names = set(SMT_KEYWORDS)
        
        # sort_registry maps an internal key to its SMT-LIB string representation.
        # e.g., {'s1': 'Int', 's2': '(Bag s1)', 's3': 'mysort'}
        self.sort_registry = {}
        
        # variables maps an internal sort key to a list of variable names of that sort.
        # e.g., {'s1': ['v1', 'v2'], 's2': ['b1']}
        self.variables = {}
        
        self.max_depth = random.randint(4, 7)
        self.min_name_len = 5
        self.max_name_len = 10

    def _generate_name(self):
        """Generates a new, unique, valid SMT-LIB identifier."""
        while True:
            length = random.randint(self.min_name_len, self.max_name_len)
            name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _initialize_state(self):
        """Sets up the initial environment of sorts and variables."""
        # 1. Add built-in sorts
        self.sort_registry['Int'] = 'Int'
        self.sort_registry['Bool'] = 'Bool'
        
        # 2. Generate 1-2 uninterpreted sorts
        num_uninterpreted_sorts = random.randint(1, 2)
        element_sort_keys = ['Int']
        for _ in range(num_uninterpreted_sorts):
            sort_key = self._generate_name()
            self.declarations.append(f"(declare-sort {sort_key} 0)")
            self.sort_registry[sort_key] = sort_key
            element_sort_keys.append(sort_key)

        # 3. Generate bag sorts for a random subset of element sorts
        num_bag_sorts = random.randint(1, len(element_sort_keys))
        for elem_sort_key in random.sample(element_sort_keys, k=num_bag_sorts):
            elem_sort_smt = self.sort_registry[elem_sort_key]
            bag_sort_smt = f"(Bag {elem_sort_smt})"
            bag_sort_key = self._generate_name() 
            self.sort_registry[bag_sort_key] = bag_sort_smt

        # 4. Populate 2-4 variables for each declared sort
        for sort_key, sort_smt in self.sort_registry.items():
            self.variables[sort_key] = []
            num_vars = random.randint(2, 4)
            for _ in range(num_vars):
                var_name = self._generate_name()
                self.declarations.append(f"(declare-const {var_name} {sort_smt})")
                self.variables[sort_key].append(var_name)

    def _get_random_sort_key(self, filter_fn=None):
        """Gets a random internal sort key, optionally filtered."""
        keys = list(self.sort_registry.keys())
        if filter_fn:
            keys = [k for k, v in self.sort_registry.items() if filter_fn(k, v)]
        return random.choice(keys) if keys else None

    def _get_random_variable(self, sort_key):
        """Gets a random variable name for a given internal sort key."""
        if sort_key in self.variables and self.variables[sort_key]:
            return random.choice(self.variables[sort_key])
        # Fallback: create a new variable on the fly. Should be rare.
        var_name = self._generate_name()
        sort_smt = self.sort_registry[sort_key]
        self.declarations.append(f"(declare-const {var_name} {sort_smt})")
        if sort_key not in self.variables: self.variables[sort_key] = []
        self.variables[sort_key].append(var_name)
        return var_name

    def _get_elem_sort_key_for_bag(self, bag_sort_key):
        """Given a bag sort key, finds the key for its element sort."""
        bag_sort_smt = self.sort_registry[bag_sort_key]
        # Assumes format "(Bag ElemSort)"
        elem_sort_smt = bag_sort_smt[5:-1]
        return next((k for k, v in self.sort_registry.items() if v == elem_sort_smt), None)

    def _generate_term(self, depth, sort_key):
        """Dispatcher to generate a term of a specific sort."""
        sort_smt = self.sort_registry[sort_key]
        if sort_smt == 'Int':
            return self._generate_int_term(depth)
        if sort_smt == 'Bool':
            return self._generate_bool_term(depth)
        if sort_smt.startswith('(Bag'):
            return self._generate_bag_term(depth, sort_key)
        # Uninterpreted sort: can only be a variable in this generator
        return self._get_random_variable(sort_key)

    def _generate_int_term(self, depth):
        """Generates a term of sort Int."""
        if depth <= 0:
            return random.choice([self._get_random_variable('Int'), str(random.randint(0, 100))])

        producers = ['var', 'numeral', 'bag.count', 'arithmetic']
        weights = [2, 2, 3, 2]
        choice = random.choices(producers, weights)[0]

        if choice == 'var': return self._get_random_variable('Int')
        if choice == 'numeral': return str(random.randint(0, 100))
        
        if choice == 'bag.count':
            bag_sort_key = self._get_random_sort_key(filter_fn=lambda k, v: v.startswith('(Bag'))
            if not bag_sort_key: return self._get_random_variable('Int')
            elem_sort_key = self._get_elem_sort_key_for_bag(bag_sort_key)
            if not elem_sort_key: return self._get_random_variable('Int')
            
            elem_term = self._generate_term(depth - 1, elem_sort_key)
            bag_term = self._generate_term(depth - 1, bag_sort_key)
            return f"(bag.count {elem_term} {bag_term})"
        
        # arithmetic
        op = random.choice(['+', '-', '*'])
        t1 = self._generate_int_term(depth - 1)
        t2 = self._generate_int_term(depth - 1)
        return f"({op} {t1} {t2})"

    def _generate_bag_term(self, depth, bag_sort_key):
        """Generates a term of a given bag sort."""
        if depth <= 0: return self._get_random_variable(bag_sort_key)

        bag_sort_smt = self.sort_registry[bag_sort_key]
        producers = ['var', 'empty', 'make', 'union_d', 'union_m', 'inter_m',
                     'diff_s', 'diff_r', 'setof', 'ite']
        weights = [2, 1, 3, 2, 2, 2, 2, 2, 1, 2]
        choice = random.choices(producers, weights)[0]

        if choice == 'var': return self._get_random_variable(bag_sort_key)
        if choice == 'empty': return f"(as bag.empty {bag_sort_smt})"
        
        if choice == 'make':
            elem_sort_key = self._get_elem_sort_key_for_bag(bag_sort_key)
            if not elem_sort_key: return self._get_random_variable(bag_sort_key)
            elem_term = self._generate_term(depth - 1, elem_sort_key)
            int_term = self._generate_int_term(depth - 1)
            return f"(bag {elem_term} {int_term})"

        if choice in ['union_d', 'union_m', 'inter_m', 'diff_s', 'diff_r']:
            op_map = {'union_d': 'bag.union_disjoint', 'union_m': 'bag.union_max',
                      'inter_m': 'bag.inter_min', 'diff_s': 'bag.difference_subtract',
                      'diff_r': 'bag.difference_remove'}
            t1 = self._generate_bag_term(depth - 1, bag_sort_key)
            t2 = self._generate_bag_term(depth - 1, bag_sort_key)
            return f"({op_map[choice]} {t1} {t2})"

        if choice == 'setof':
            t1 = self._generate_bag_term(depth - 1, bag_sort_key)
            return f"(bag.setof {t1})"

        if choice == 'ite':
            cond = self._generate_bool_term(depth - 1)
            t1 = self._generate_bag_term(depth - 1, bag_sort_key)
            t2 = self._generate_bag_term(depth - 1, bag_sort_key)
            return f"(ite {cond} {t1} {t2})"
        
        return self._get_random_variable(bag_sort_key) # Fallback

    def _generate_predicate(self, depth):
        """Generates a predicate (a term that evaluates to Bool)."""
        # At depth 0, we must produce a non-recursive predicate.
        if depth <= 0:
            sort_key = self._get_random_sort_key()
            if not sort_key: return "true"
            v1 = self._get_random_variable(sort_key)
            v2 = self._get_random_variable(sort_key)
            return f"(= {v1} {v2})"

        producers = ['=', 'distinct', 'bag.member', 'bag.subbag']
        weights = [4, 1, 3, 3]
        choice = random.choices(producers, weights)[0]

        if choice == '=':
            sort_key = self._get_random_sort_key()
            if not sort_key: return "true"
            t1 = self._generate_term(depth - 1, sort_key)
            t2 = self._generate_term(depth - 1, sort_key)
            return f"(= {t1} {t2})"

        if choice == 'distinct':
            sort_key = self._get_random_sort_key()
            if not sort_key: return "true"
            terms = [self._generate_term(depth - 1, sort_key) for _ in range(random.randint(2, 4))]
            return f"(distinct {' '.join(terms)})"

        bag_sort_key = self._get_random_sort_key(filter_fn=lambda k, v: v.startswith('(Bag'))
        if not bag_sort_key: return "true" # Fallback if no bag sorts exist

        if choice == 'bag.member':
            elem_sort_key = self._get_elem_sort_key_for_bag(bag_sort_key)
            if not elem_sort_key: return "true"
            elem = self._generate_term(depth - 1, elem_sort_key)
            bag = self._generate_term(depth - 1, bag_sort_key)
            return f"(bag.member {elem} {bag})"

        if choice == 'bag.subbag':
            b1 = self._generate_term(depth - 1, bag_sort_key)
            b2 = self._generate_term(depth - 1, bag_sort_key)
            return f"(bag.subbag {b1} {b2})"
        
        return "true" # Should not be reached

    def _generate_bool_term(self, depth):
        """Generates a term of sort Bool, the start symbol of the grammar."""
        if depth <= 0:
            options = ['predicate', 'literal', 'var']
            choice = random.choices(options, weights=[3, 1, 2])[0]
            if choice == 'predicate': return self._generate_predicate(0)
            if choice == 'literal': return random.choice(['true', 'false'])
            return self._get_random_variable('Bool')

        producers = ['predicate', 'literal', 'var', 'not', 'n_ary', 'ite']
        weights = [4, 1, 2, 3, 4, 3]
        choice = random.choices(producers, weights)[0]

        if choice == 'predicate': return self._generate_predicate(depth - 1)
        if choice == 'literal': return random.choice(['true', 'false'])
        if choice == 'var': return self._get_random_variable('Bool')
        
        if choice == 'not':
            sub = self._generate_bool_term(depth - 1)
            return f"(not {sub})"

        if choice == 'n_ary':
            op = random.choice(['and', 'or', 'xor', '=>'])
            terms = [self._generate_bool_term(depth - 1) for _ in range(random.randint(2, 4))]
            return f"({op} {' '.join(terms)})"

        if choice == 'ite':
            cond = self._generate_bool_term(depth - 1)
            t1 = self._generate_bool_term(depth - 1)
            t2 = self._generate_bool_term(depth - 1)
            return f"(ite {cond} {t1} {t2})"
        
        return "true" # Fallback

    def generate(self):
        """Main generation entry point."""
        self._initialize_state()
        formula = self._generate_bool_term(self.max_depth)
        decls_str = "\n".join(self.declarations)
        return decls_str, formula


def generate_bags_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula for the Bags theory,
    returning the necessary declarations and the formula term itself.

    This function follows a specified Context-Free Grammar to ensure syntactic
    correctness and aims for diversity in the generated structures.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): A string of SMT-LIB2 declarations for all sorts and
          constants used in the formula.
        - formula (str): A string representing a single SMT-LIB2 Boolean term.
    """
    generator = _FormulaGenerator()
    return generator.generate()