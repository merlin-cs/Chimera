# complete Python module
import random

# SMT-LIB keywords and other reserved words to avoid for generated names.
SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "true", "false", "ite", "let", "exists", "forall",
    "match", "assert", "check-sat", "declare-sort", "declare-fun", "define-fun",
    "get-value", "get-model", "exit", "set-logic", "set-option", "set-info",
    "Int", "Bool", "Real", "String", "Array", "Set", "Relation", "Tuple", "UnitTuple",
    "set.empty", "as", "set.universe", "set.singleton", "set.insert", "set.union",
    "set.inter", "set.minus", "set.complement", "set.member", "set.subset",
    "set.card", "set.is_empty", "set.is_singleton", "rel.transpose", "rel.tclosure",
    "rel.join", "rel.product", "tuple", "tuple.unit", "tuple.select", "_",
    "distinct", "="
}

class _FormulaGenerator:
    """
    A class to generate random, well-typed SMT-LIB2 formulas for Sets and Relations.
    This class is intended for internal use by the public generator function.
    """

    def __init__(self):
        self.random = random
        self.max_depth = self.random.randint(4, 7)
        self.max_arity = 3
        
        self.declarations = []
        self.declared_names = set(SMT_KEYWORDS)
        
        # { sort_str: {'type': 'base'|'set'|'tuple', ...details...} }
        self.sorts = {} 
        # { name: {'args': [sorts], 'ret': sort} }
        self.functions = {}
        
        self._initialize_environment()

    def _generate_name(self):
        """Generates a new random name that is not a keyword or already used."""
        while True:
            length = self.random.randint(5, 10)
            name = "".join(self.random.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(length))
            if name not in self.declared_names:
                self.declared_names.add(name)
                return name

    def _initialize_environment(self):
        """Sets up the initial sorts, constants, and functions."""
        # Built-in sorts
        self.sorts['Bool'] = {'type': 'bool'}
        self.sorts['Int'] = {'type': 'int'}

        # Create a few base uninterpreted sorts
        for _ in range(self.random.randint(1, 2)):
            self._create_sort('base')

        # Create a few initial set and tuple sorts to ensure they are available
        for _ in range(self.random.randint(1, 2)):
            self._create_sort('set')
        for _ in range(self.random.randint(1, 2)):
            self._create_sort('tuple')

        # Create some initial constants for various sorts
        all_sorts = list(self.sorts.keys())
        for s in all_sorts:
            if s == 'Bool': continue
            if self.random.random() < 0.5:
                self._create_constant(s)

    def _create_sort(self, sort_type=None):
        """Creates a sort of a given type and adds its declaration if necessary."""
        if sort_type is None:
            sort_type = self.random.choice(['base', 'set', 'tuple'])

        if sort_type == 'base':
            name = self._generate_name()
            self.declarations.append(f"(declare-sort {name} 0)")
            self.sorts[name] = {'type': 'base'}
            return name
        
        if sort_type == 'set':
            element_sort = self._get_random_sort()
            if self.random.random() < 0.3: # Relation
                arity = self.random.randint(1, self.max_arity)
                element_sorts = [self._get_random_sort() for _ in range(arity)]
                tuple_sort_str = f"(Tuple {' '.join(element_sorts)})"
                if tuple_sort_str not in self.sorts:
                     self.sorts[tuple_sort_str] = {'type': 'tuple', 'elements': element_sorts}
                sort_str = f"(Relation {' '.join(element_sorts)})"
                if sort_str not in self.sorts:
                    self.sorts[sort_str] = {'type': 'set', 'element': tuple_sort_str, 'relation_elements': element_sorts}
                return sort_str
            else: # Set
                sort_str = f"(Set {element_sort})"
                if sort_str not in self.sorts:
                    self.sorts[sort_str] = {'type': 'set', 'element': element_sort}
                return sort_str

        if sort_type == 'tuple':
            if self.random.random() < 0.2:
                if 'UnitTuple' not in self.sorts:
                    self.sorts['UnitTuple'] = {'type': 'tuple', 'elements': []}
                return 'UnitTuple'
            arity = self.random.randint(1, self.max_arity)
            element_sorts = [self._get_random_sort() for _ in range(arity)]
            sort_str = f"(Tuple {' '.join(element_sorts)})"
            if sort_str not in self.sorts:
                self.sorts[sort_str] = {'type': 'tuple', 'elements': element_sorts}
            return sort_str
        
        raise ValueError(f"Unknown sort type: {sort_type}")

    def _create_constant(self, sort_str):
        """Declares a new constant of a given sort."""
        name = self._generate_name()
        self.declarations.append(f"(declare-const {name} {sort_str})")
        self.functions[name] = {'args': [], 'ret': sort_str}
        return name

    # --- Sort Utilities ---

    def _get_sort_type(self, sort_str):
        return self.sorts.get(sort_str, {}).get('type', 'unknown')

    def _get_random_sort(self, of_type=None):
        """Gets a random sort string, optionally filtered by type."""
        choices = list(self.sorts.keys())
        if of_type:
            choices = [s for s in choices if self._get_sort_type(s) == of_type]
        
        if not choices:
            # If no sort of the required type exists, create one.
            return self._create_sort(sort_type=of_type)
        return self.random.choice(choices)

    def _get_set_element_sort(self, set_sort_str):
        """Extracts the element sort from a set or relation sort string."""
        return self.sorts[set_sort_str]['element']
    
    def _is_relation_sort(self, sort_str):
        return 'relation_elements' in self.sorts.get(sort_str, {})

    # --- Term Generation ---

    def _find_symbols_of_sort(self, target_sort, scope):
        """Finds available variables/constants of a target sort."""
        symbols = []
        # Local scope (quantified variables)
        for name, sort in scope.items():
            if sort == target_sort:
                symbols.append(name)
        # Global scope (constants)
        for name, sig in self.functions.items():
            if not sig['args'] and sig['ret'] == target_sort:
                symbols.append(name)
        return symbols

    def _gen_terminal(self, target_sort, scope):
        """Generates a terminal term of the target sort."""
        # Prefer existing symbols
        symbols = self._find_symbols_of_sort(target_sort, scope)
        
        # Add literals for specific sorts
        if target_sort == 'Bool':
            symbols.extend(['true', 'false'])
        elif target_sort == 'Int':
            symbols.append(str(self.random.randint(-100, 100)))
        elif target_sort == 'UnitTuple':
            symbols.append('tuple.unit')
        
        if symbols:
            return self.random.choice(symbols)
        
        # Fallback: if no symbol exists, create one
        if target_sort.startswith('(Set'):
            element_sort = self._get_set_element_sort(target_sort)
            return f"(as set.empty (Set {element_sort}))"
        
        return self._create_constant(target_sort)

    def _gen_term(self, depth, target_sort, scope):
        """The main recursive function to generate a term of a target sort."""
        if depth >= self.max_depth:
            return self._gen_terminal(target_sort, scope)

        sort_type = self._get_sort_type(target_sort)
        
        # Weighted list of production functions for each sort type
        # Each tuple is (production_function, weight)
        prods = {
            'bool': [
                (self._prod_bool_literal, 5), (self._prod_not, 10), (self._prod_connective, 15),
                (self._prod_equals, 15), (self._prod_distinct, 5), (self._prod_set_member, 10),
                (self._prod_set_subset, 10), (self._prod_set_is_empty, 5), (self._prod_set_is_singleton, 5),
                (self._prod_quantifier, 5),
            ],
            'set': [
                (self._prod_set_empty, 5), (self._prod_set_universe, 2), (self._prod_set_singleton, 10),
                (self._prod_set_insert, 15), (self._prod_set_union_inter, 15), (self._prod_set_minus, 10),
                (self._prod_set_complement, 5),
            ],
            'tuple': [
                (self._prod_tuple_constructor, 20), (self._prod_tuple_unit, 5),
            ],
            'int': [
                (self._prod_int_literal, 15), (self._prod_set_card, 10),
            ],
            'base': [
                (self._prod_tuple_select, 10),
            ]
        }
        
        # Add relation-specific productions
        if sort_type == 'set' and self._is_relation_sort(target_sort):
            prods['set'].extend([
                (self._prod_rel_transpose, 5), (self._prod_rel_tclosure, 3),
                (self._prod_rel_join, 5), (self._prod_rel_product, 5),
            ])

        # Add generic productions (variables/constants) for all types
        if sort_type in prods:
            prods[sort_type].append((self._prod_var, 20))
        else: # Should only be for 'base' if its list was empty
            prods[sort_type] = [(self._prod_var, 20)]

        # Filter productions to what's possible
        possible_prods_with_weights = [p for p in prods.get(sort_type, []) if p[0] is not None]

        # If no productions match, generate a terminal
        if not possible_prods_with_weights:
            return self._gen_terminal(target_sort, scope)

        production_funcs, weights = zip(*possible_prods_with_weights)
        chosen_prod = self.random.choices(production_funcs, weights=weights, k=1)[0]
        
        return chosen_prod(depth, target_sort, scope)

    # --- Production Implementations ---

    # Generic
    def _prod_var(self, depth, target_sort, scope):
        return self._gen_terminal(target_sort, scope)

    # Boolean Productions
    def _prod_bool_literal(self, depth, target_sort, scope):
        return self.random.choice(['true', 'false'])

    def _prod_not(self, depth, target_sort, scope):
        sub_term = self._gen_term(depth + 1, 'Bool', scope)
        return f"(not {sub_term})"

    def _prod_connective(self, depth, target_sort, scope):
        op = self.random.choice(['and', 'or', 'xor', '=>'])
        arity = self.random.randint(2, self.max_arity)
        args = [self._gen_term(depth + 1, 'Bool', scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _prod_equals(self, depth, target_sort, scope):
        # Equality can be over any sort
        arg_sort = self._get_random_sort()
        arg1 = self._gen_term(depth + 1, arg_sort, scope)
        arg2 = self._gen_term(depth + 1, arg_sort, scope)
        return f"(= {arg1} {arg2})"

    def _prod_distinct(self, depth, target_sort, scope):
        arg_sort = self._get_random_sort()
        arity = self.random.randint(2, self.max_arity + 1)
        args = [self._gen_term(depth + 1, arg_sort, scope) for _ in range(arity)]
        return f"(distinct {' '.join(args)})"

    def _prod_set_member(self, depth, target_sort, scope):
        set_sort = self._get_random_sort(of_type='set')
        element_sort = self._get_set_element_sort(set_sort)
        set_term = self._gen_term(depth + 1, set_sort, scope)
        element_term = self._gen_term(depth + 1, element_sort, scope)
        return f"(set.member {element_term} {set_term})"

    def _prod_set_subset(self, depth, target_sort, scope):
        set_sort = self._get_random_sort(of_type='set')
        set1 = self._gen_term(depth + 1, set_sort, scope)
        set2 = self._gen_term(depth + 1, set_sort, scope)
        return f"(set.subset {set1} {set2})"

    def _prod_set_is_empty(self, depth, target_sort, scope):
        set_sort = self._get_random_sort(of_type='set')
        set_term = self._gen_term(depth + 1, set_sort, scope)
        return f"(set.is_empty {set_term})"
    
    def _prod_set_is_singleton(self, depth, target_sort, scope):
        set_sort = self._get_random_sort(of_type='set')
        set_term = self._gen_term(depth + 1, set_sort, scope)
        return f"(set.is_singleton {set_term})"

    def _prod_quantifier(self, depth, target_sort, scope):
        op = self.random.choice(['forall', 'exists'])
        arity = self.random.randint(1, self.max_arity)
        new_scope = scope.copy()
        sorted_vars = []
        for _ in range(arity):
            var_name = self._generate_name()
            var_sort = self._get_random_sort()
            new_scope[var_name] = var_sort
            sorted_vars.append(f"({var_name} {var_sort})")
        
        body = self._gen_term(depth + 1, 'Bool', new_scope)
        return f"({op} ({' '.join(sorted_vars)}) {body})"

    # Set Productions
    def _prod_set_empty(self, depth, target_sort, scope):
        element_sort = self._get_set_element_sort(target_sort)
        return f"(as set.empty (Set {element_sort}))"

    def _prod_set_universe(self, depth, target_sort, scope):
        element_sort = self._get_set_element_sort(target_sort)
        return f"(as set.universe (Set {element_sort}))"

    def _prod_set_singleton(self, depth, target_sort, scope):
        element_sort = self._get_set_element_sort(target_sort)
        element_term = self._gen_term(depth + 1, element_sort, scope)
        return f"(set.singleton {element_term})"

    def _prod_set_insert(self, depth, target_sort, scope):
        element_sort = self._get_set_element_sort(target_sort)
        arity = self.random.randint(1, self.max_arity)
        elements = [self._gen_term(depth + 1, element_sort, scope) for _ in range(arity)]
        set_term = self._gen_term(depth + 1, target_sort, scope)
        return f"(set.insert {' '.join(elements)} {set_term})"

    def _prod_set_union_inter(self, depth, target_sort, scope):
        op = self.random.choice(['set.union', 'set.inter'])
        arity = self.random.randint(2, self.max_arity)
        args = [self._gen_term(depth + 1, target_sort, scope) for _ in range(arity)]
        return f"({op} {' '.join(args)})"

    def _prod_set_minus(self, depth, target_sort, scope):
        arg1 = self._gen_term(depth + 1, target_sort, scope)
        arg2 = self._gen_term(depth + 1, target_sort, scope)
        return f"(set.minus {arg1} {arg2})"

    def _prod_set_complement(self, depth, target_sort, scope):
        arg = self._gen_term(depth + 1, target_sort, scope)
        return f"(set.complement {arg})"

    # Relation Productions
    def _prod_rel_transpose(self, depth, target_sort, scope):
        # rel.transpose is only valid for binary relations
        elements = self.sorts[target_sort].get('relation_elements')
        if not elements or len(elements) != 2:
            return self._gen_terminal(target_sort, scope) # Cannot generate, fallback
        
        arg = self._gen_term(depth + 1, target_sort, scope)
        return f"(rel.transpose {arg})"

    def _prod_rel_tclosure(self, depth, target_sort, scope):
        # rel.tclosure is only valid for binary relations on the same type (T, T)
        elements = self.sorts[target_sort].get('relation_elements')
        if not elements or len(elements) != 2 or elements[0] != elements[1]:
            return self._gen_terminal(target_sort, scope) # Fallback
            
        arg = self._gen_term(depth + 1, target_sort, scope)
        return f"(rel.tclosure {arg})"

    def _prod_rel_join(self, depth, target_sort, scope):
        # join needs (Rel A B) and (Rel B C) to produce (Rel A C)
        # For simplicity, we'll join two relations of the same sort (Rel A B) x (Rel A B)
        # SMT solvers should reject this if B != A. This is valid for fuzzing.
        arg1 = self._gen_term(depth + 1, target_sort, scope)
        arg2 = self._gen_term(depth + 1, target_sort, scope)
        return f"(rel.join {arg1} {arg2})"

    def _prod_rel_product(self, depth, target_sort, scope):
        # rel.product needs (Set A) and (Set B) to produce (Rel A B)
        target_elements = self.sorts[target_sort].get('relation_elements')
        if not target_elements or len(target_elements) != 2:
            return self._gen_terminal(target_sort, scope) # Fallback
        
        sort_A, sort_B = target_elements
        set_sort_A = f"(Set {sort_A})"
        set_sort_B = f"(Set {sort_B})"
        
        # Ensure these set sorts exist
        if set_sort_A not in self.sorts: self.sorts[set_sort_A] = {'type': 'set', 'element': sort_A}
        if set_sort_B not in self.sorts: self.sorts[set_sort_B] = {'type': 'set', 'element': sort_B}

        arg1 = self._gen_term(depth + 1, set_sort_A, scope)
        arg2 = self._gen_term(depth + 1, set_sort_B, scope)
        return f"(rel.product {arg1} {arg2})"

    # Tuple Productions
    def _prod_tuple_constructor(self, depth, target_sort, scope):
        elements = self.sorts[target_sort].get('elements')
        if not elements: # UnitTuple case handled separately
            return self._gen_terminal(target_sort, scope)
        
        args = [self._gen_term(depth + 1, s, scope) for s in elements]
        return f"(tuple {' '.join(args)})"

    def _prod_tuple_unit(self, depth, target_sort, scope):
        return "tuple.unit"

    # Int/Base Productions
    def _prod_int_literal(self, depth, target_sort, scope):
        return str(self.random.randint(-100, 100))

    def _prod_set_card(self, depth, target_sort, scope):
        set_sort = self._get_random_sort(of_type='set')
        set_term = self._gen_term(depth + 1, set_sort, scope)
        return f"(set.card {set_term})"

    def _prod_tuple_select(self, depth, target_sort, scope):
        # Find a tuple sort that contains the target_sort
        possible_tuples = []
        for sort_str, sort_info in self.sorts.items():
            if sort_info['type'] == 'tuple' and target_sort in sort_info.get('elements', []):
                possible_tuples.append(sort_str)
        
        if not possible_tuples:
            return self._gen_terminal(target_sort, scope) # Fallback
        
        tuple_sort = self.random.choice(possible_tuples)
        tuple_elements = self.sorts[tuple_sort]['elements']
        
        # Find all indices where target_sort appears
        indices = [i for i, s in enumerate(tuple_elements) if s == target_sort]
        index = self.random.choice(indices)
        
        tuple_term = self._gen_term(depth + 1, tuple_sort, scope)
        return f"((_ tuple.select {index}) {tuple_term})"

    def generate(self):
        """Generates the full formula and declarations."""
        formula = self._gen_term(depth=0, target_sort='Bool', scope={})
        
        # Post-process declarations to ensure order (sorts first)
        decls_sorted = sorted(list(set(self.declarations)), key=lambda x: 0 if x.startswith('(declare-sort') else 1)
        
        return "\n".join(decls_sorted), formula


def generate_setsandrelations_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula for the Sets_and_Relations theory.

    This function implements a generator based on a CFG for Boolean terms in the
    Sets_and_Relations theory. It randomizes the structure, operators, and variables
    to produce a diverse range of formulas for testing SMT solvers.

    Returns:
        A tuple (decls, formula), where:
        - decls (str): A string of SMT-LIB2 declarations for all sorts, constants,
          and functions used in the formula.
        - formula (str): A string containing a single, well-formed SMT-LIB2
          Boolean term.
    """
    generator = _FormulaGenerator()
    decls, formula = generator.generate()
    return decls, formula