# complete Python module
import random
import string

# SMT-LIB keywords to avoid as symbol names
_SMT_KEYWORDS = {
    "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-sort", "echo",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-core", "get-value", "pop", "push",
    "reset", "reset-assertions", "set-info", "set-logic", "set-option",
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "=", "distinct",
    "forall", "exists", "let", "select", "store", "as", "Int", "Real", "Bool",
    "Array", "BitVec", "continued-execution", "error", "immediate-exit",
    "incomplete", "logic", "memout", "sat", "success", "theory", "unknown",
    "unsupported", "unsat", "par", "NUMERAL", "DECIMAL", "STRING", "abs",
    "div", "mod", "rem", "to_real", "to_int", "is_int", "bvadd", "bvsub",
    "bvmul", "bvudiv", "bvsdiv", "bvurem", "bvsrem", "bvand", "bvor",
    "bvxor", "bvnot", "bvneg", "concat", "extract", "sign_extend",
    "zero_extend", "rotate_left", "rotate_right"
}

class _Generator:
    """Internal class to manage state for a single formula generation."""

    def __init__(self):
        self.max_depth = random.randint(4, 7)
        self.used_names = set(_SMT_KEYWORDS)
        self.declarations = []
        
        self.sorts = {'Bool': 'Bool', 'Int': 'Int', 'Real': 'Real'}
        self.sort_names = ['Bool', 'Int', 'Real']

        self.symbols = {}
        self.scoped_symbols = []

    def _generate_unique_name(self, prefix='v'):
        while True:
            name = prefix + ''.join(random.choices(string.ascii_lowercase, k=random.randint(4, 8)))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _format_sort(self, sort):
        if isinstance(sort, tuple):
            return f"({' '.join(self._format_sort(s) for s in sort)})"
        return sort

    def _initialize_context(self):
        """Generates random sorts, constants, and functions for the formula."""
        # 1. Generate base sorts
        for _ in range(random.randint(1, 2)):
            sort_name = self._generate_unique_name('s')
            self.sorts[sort_name] = sort_name
            self.sort_names.append(sort_name)
            self.declarations.append(f"(declare-sort {sort_name} 0)")

        # 2. Generate array sorts
        base_sorts = [s for s in self.sort_names if s != 'Bool']
        if not base_sorts: base_sorts = ['Int']
        
        for _ in range(random.randint(1, 3)):
            index_sort = random.choice(base_sorts)
            elem_sort = random.choice(base_sorts)
            
            array_sort_name = self._generate_unique_name('a')
            array_sort_val = ('Array', index_sort, elem_sort)
            self.sorts[array_sort_name] = array_sort_val
            self.sort_names.append(array_sort_name)

        # 3. Generate constants (ensure at least one per non-Bool sort)
        for sort_name, sort_val in self.sorts.items():
            if sort_val == 'Bool': continue
            const_name = self._generate_unique_name('c')
            self.symbols[const_name] = {'type': 'const', 'sort': sort_val}
            self.declarations.append(f"(declare-const {const_name} {self._format_sort(sort_val)})")

        # 4. Generate functions
        for _ in range(random.randint(1, 3)):
            fun_name = self._generate_unique_name('f')
            param_sorts = [self.sorts[random.choice(self.sort_names)] for _ in range(random.randint(1, 3))]
            return_sort = self.sorts[random.choice(self.sort_names)]
            
            self.symbols[fun_name] = {'type': 'fun', 'params': param_sorts, 'return': return_sort}
            param_sorts_str = ' '.join(self._format_sort(s) for s in param_sorts)
            return_sort_str = self._format_sort(return_sort)
            self.declarations.append(f"(declare-fun {fun_name} ({param_sorts_str}) {return_sort_str})")

    def _get_symbols_of_sort(self, target_sort):
        """Finds all available symbols (vars, consts) that match the target_sort."""
        candidates = []
        for scope in reversed(self.scoped_symbols):
            for name, info in scope.items():
                if info['sort'] == target_sort:
                    candidates.append(name)
        
        for name, info in self.symbols.items():
            if info['type'] == 'const' and info['sort'] == target_sort:
                candidates.append(name)
        return candidates

    def _generate_term(self, sort, depth):
        """Dispatcher to generate a term of a given sort."""
        if sort == 'Bool':
            return self._generate_bool_term(depth)
        elif isinstance(sort, tuple) and sort[0] == 'Array':
            return self._generate_array_term(sort, depth)
        else:
            return self._generate_base_term(sort, depth)

    def _generate_bool_term(self, depth):
        if depth >= self.max_depth:
            candidates = self._get_symbols_of_sort('Bool')
            if candidates:
                return random.choice(candidates)
            return random.choice(['true', 'false'])

        productions = {
            'const': 2, 'var': 4, 'not': 3, 'nary': 5, 'implies': 3,
            'ite': 3, 'eq': 6, 'distinct': 2, 'quant': 2, 'let': 1, 'fun_call': 2
        }
        
        if not self._get_symbols_of_sort('Bool'): productions.pop('var', None)
        if not any(s['type'] == 'fun' and s['return'] == 'Bool' for s in self.symbols.values()):
            productions.pop('fun_call', None)

        prod_names, prod_weights = zip(*productions.items())
        chosen_prod = random.choices(prod_names, weights=prod_weights, k=1)[0]

        if chosen_prod == 'const': return random.choice(['true', 'false'])
        if chosen_prod == 'var': return random.choice(self._get_symbols_of_sort('Bool'))
        if chosen_prod == 'not': return f"(not {self._generate_bool_term(depth + 1)})"
        if chosen_prod == 'nary':
            op = random.choice(['and', 'or', 'xor'])
            args = [self._generate_bool_term(depth + 1) for _ in range(random.randint(2, 4))]
            return f"({op} {' '.join(args)})"
        if chosen_prod == 'implies':
            return f"(=> {self._generate_bool_term(depth + 1)} {self._generate_bool_term(depth + 1)})"
        if chosen_prod == 'ite':
            return f"(ite {self._generate_bool_term(depth + 1)} {self._generate_bool_term(depth + 1)} {self._generate_bool_term(depth + 1)})"
        if chosen_prod == 'eq':
            sorts = list(self.sorts.values())
            weights = [3 if isinstance(s, tuple) and s[0] == 'Array' else 1 for s in sorts]
            chosen_sort = random.choices(sorts, weights=weights, k=1)[0]
            t1 = self._generate_term(chosen_sort, depth + 1)
            t2 = self._generate_term(chosen_sort, depth + 1)
            return f"(= {t1} {t2})"
        if chosen_prod == 'distinct':
            chosen_sort = random.choice(list(self.sorts.values()))
            args = [self._generate_term(chosen_sort, depth + 1) for _ in range(random.randint(2, 4))]
            return f"(distinct {' '.join(args)})"
        if chosen_prod == 'quant': return self._generate_quantifier(depth)
        if chosen_prod == 'let': return self._generate_let_binding('Bool', depth)
        if chosen_prod == 'fun_call': return self._generate_function_call('Bool', depth)
        return 'true'

    def _generate_array_term(self, sort, depth):
        if depth >= self.max_depth:
            return random.choice(self._get_symbols_of_sort(sort))

        productions = {'var': 5, 'store': 6, 'ite': 3, 'let': 1, 'fun_call': 2}
        if not any(s['type'] == 'fun' and s['return'] == sort for s in self.symbols.values()):
            productions.pop('fun_call', None)

        prod_names, prod_weights = zip(*productions.items())
        chosen_prod = random.choices(prod_names, weights=prod_weights, k=1)[0]
        
        if chosen_prod == 'var': return random.choice(self._get_symbols_of_sort(sort))
        if chosen_prod == 'store':
            _, index_sort, elem_sort = sort
            arr = self._generate_term(sort, depth + 1)
            idx = self._generate_term(index_sort, depth + 1)
            val = self._generate_term(elem_sort, depth + 1)
            return f"(store {arr} {idx} {val})"
        if chosen_prod == 'ite':
            cond = self._generate_bool_term(depth + 1)
            then_t = self._generate_term(sort, depth + 1)
            else_t = self._generate_term(sort, depth + 1)
            return f"(ite {cond} {then_t} {else_t})"
        if chosen_prod == 'let': return self._generate_let_binding(sort, depth)
        if chosen_prod == 'fun_call': return self._generate_function_call(sort, depth)
        return random.choice(self._get_symbols_of_sort(sort))

    def _generate_base_term(self, sort, depth):
        if depth >= self.max_depth:
            candidates = self._get_symbols_of_sort(sort)
            if sort == 'Int' and random.random() < 0.5: return str(random.randint(-100, 100))
            if sort == 'Real' and random.random() < 0.5: return f"{random.uniform(-100.0, 100.0):.2f}"
            return random.choice(candidates)

        productions = {'var': 5, 'select': 6, 'ite': 3, 'let': 1, 'fun_call': 3}
        if sort == 'Int': productions['literal'] = 2
        if sort == 'Real': productions['literal'] = 2
        
        if not any(isinstance(s, tuple) and s[0] == 'Array' and s[2] == sort for s in self.sorts.values()):
            productions.pop('select', None)
        if not any(s['type'] == 'fun' and s['return'] == sort for s in self.symbols.values()):
            productions.pop('fun_call', None)

        if not productions: return random.choice(self._get_symbols_of_sort(sort))

        prod_names, prod_weights = zip(*productions.items())
        chosen_prod = random.choices(prod_names, weights=prod_weights, k=1)[0]

        if chosen_prod == 'var': return random.choice(self._get_symbols_of_sort(sort))
        if chosen_prod == 'literal':
            if sort == 'Int': return str(random.randint(-100, 100))
            if sort == 'Real': return f"{random.uniform(-100.0, 100.0):.2f}"
        if chosen_prod == 'select':
            possible_arrays = [s for s in self.sorts.values() if isinstance(s, tuple) and s[0] == 'Array' and s[2] == sort]
            array_sort = random.choice(possible_arrays)
            _, index_sort, _ = array_sort
            arr = self._generate_term(array_sort, depth + 1)
            idx = self._generate_term(index_sort, depth + 1)
            return f"(select {arr} {idx})"
        if chosen_prod == 'ite':
            cond = self._generate_bool_term(depth + 1)
            then_t = self._generate_term(sort, depth + 1)
            else_t = self._generate_term(sort, depth + 1)
            return f"(ite {cond} {then_t} {else_t})"
        if chosen_prod == 'let': return self._generate_let_binding(sort, depth)
        if chosen_prod == 'fun_call': return self._generate_function_call(sort, depth)
        return random.choice(self._get_symbols_of_sort(sort))

    def _generate_quantifier(self, depth):
        quantifier = random.choice(["forall", "exists"])
        new_scope, sorted_vars_str = {}, []
        available_sorts = [s for s in self.sorts.values() if s != 'Bool'] or ['Int']

        for _ in range(random.randint(1, 2)):
            var_name = self._generate_unique_name('q')
            var_sort = random.choice(available_sorts)
            new_scope[var_name] = {'type': 'var', 'sort': var_sort}
            sorted_vars_str.append(f"({var_name} {self._format_sort(var_sort)})")
        
        self.scoped_symbols.append(new_scope)
        body = self._generate_bool_term(depth + 1)
        self.scoped_symbols.pop()
        
        return f"({quantifier} ({' '.join(sorted_vars_str)}) {body})"

    def _generate_let_binding(self, return_sort, depth):
        new_scope, bindings_str = {}, []
        
        for _ in range(random.randint(1, 2)):
            var_name = self._generate_unique_name('l')
            var_sort = random.choice(list(self.sorts.values()))
            term_val = self._generate_term(var_sort, depth + 1)
            new_scope[var_name] = {'type': 'var', 'sort': var_sort}
            bindings_str.append(f"({var_name} {term_val})")

        self.scoped_symbols.append(new_scope)
        body = self._generate_term(return_sort, depth + 1)
        self.scoped_symbols.pop()

        return f"(let ({' '.join(bindings_str)}) {body})"

    def _generate_function_call(self, return_sort, depth):
        possible_funcs = [name for name, info in self.symbols.items() if info['type'] == 'fun' and info['return'] == return_sort]
        fun_name = random.choice(possible_funcs)
        fun_info = self.symbols[fun_name]
        
        args = [self._generate_term(ps, depth + 1) for ps in fun_info['params']]
        return f"({fun_name} {' '.join(args)})"

    def generate(self):
        """Main generation entry point for the class."""
        self._initialize_context()
        formula = self._generate_bool_term(0)
        decls_str = "\n".join(self.declarations)
        return decls_str, formula


def generate_arrayex_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula for the ArraysEx theory.

    This function implements a random generator based on a context-free grammar
    for Boolean terms in SMT-LIB, ensuring that all generated terms are
    syntactically correct and well-typed according to the generated declarations.

    Returns:
        A tuple (decls, formula), where:
        - decls (str): A string of SMT-LIB2 declarations for all sorts,
          constants, and functions used in the formula.
        - formula (str): A string representing a single SMT-LIB2 Boolean term.
    """
    generator = _Generator()
    return generator.generate()