import random

# ============================================================================
# SMT-LIB Sets and Relations Random Formula Generator
# ============================================================================

# Reserved SMT-LIB keywords to avoid
RESERVED_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', 'exists', 'forall',
    'let', 'as', 'set', 'rel', 'tuple', 'Int', 'Bool', 'Set', 'Relation',
    'Tuple', 'distinct', 'div', 'mod', 'member', 'subset', 'empty',
    'universe', 'singleton', 'union', 'inter', 'minus', 'complement',
    'insert', 'card', 'transpose', 'tclosure', 'join', 'product',
    'select', 'unit', 'UnitTuple'
}

# ============================================================================
# Name Generation
# ============================================================================

def generate_random_name(min_length=5):
    """Generate a random lowercase identifier of at least min_length characters."""
    while True:
        length = random.randint(min_length, min_length + 5)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in RESERVED_KEYWORDS:
            return name

# ============================================================================
# Sort Management
# ============================================================================

class SortManager:
    def __init__(self):
        self.base_sorts = ['Int', 'Bool']
        self.user_sorts = []
        self.set_sorts = []
        self.tuple_sorts = []
        self.relation_sorts = []
        
    def get_random_base_sort(self):
        return random.choice(self.base_sorts)
    
    def create_user_sort(self):
        name = generate_random_name()
        self.user_sorts.append(name)
        return name
    
    def get_random_sort(self, allow_complex=True):
        if not allow_complex:
            return self.get_random_base_sort()
        
        choices = self.base_sorts + self.user_sorts
        if self.set_sorts:
            choices.extend(self.set_sorts)
        if self.tuple_sorts:
            choices.extend(self.tuple_sorts)
        
        return random.choice(choices) if choices else 'Int'
    
    def create_set_sort(self, elem_sort):
        sort_str = f"(Set {elem_sort})"
        self.set_sorts.append(sort_str)
        return sort_str
    
    def create_tuple_sort(self, sorts):
        sort_str = f"(Tuple {' '.join(sorts)})"
        self.tuple_sorts.append(sort_str)
        return sort_str
    
    def create_relation_sort(self, sorts):
        sort_str = f"(Relation {' '.join(sorts)})"
        self.relation_sorts.append(sort_str)
        return sort_str

# ============================================================================
# Variable and Declaration Management
# ============================================================================

class SymbolTable:
    def __init__(self, sort_manager):
        self.sort_manager = sort_manager
        self.int_vars = []
        self.bool_vars = []
        self.set_vars = []
        self.relation_vars = []
        self.tuple_vars = []
        self.declarations = []
        
    def declare_int_var(self):
        name = generate_random_name()
        self.int_vars.append(name)
        self.declarations.append(f"(declare-const {name} Int)")
        return name
    
    def declare_bool_var(self):
        name = generate_random_name()
        self.bool_vars.append(name)
        self.declarations.append(f"(declare-const {name} Bool)")
        return name
    
    def declare_set_var(self, elem_sort='Int'):
        name = generate_random_name()
        sort = self.sort_manager.create_set_sort(elem_sort)
        self.set_vars.append((name, sort))
        self.declarations.append(f"(declare-const {name} {sort})")
        return name, sort
    
    def declare_relation_var(self, sorts):
        name = generate_random_name()
        sort = self.sort_manager.create_relation_sort(sorts)
        self.relation_vars.append((name, sort))
        self.declarations.append(f"(declare-const {name} {sort})")
        return name, sort
    
    def declare_tuple_var(self, sorts):
        name = generate_random_name()
        sort = self.sort_manager.create_tuple_sort(sorts)
        self.tuple_vars.append((name, sort))
        self.declarations.append(f"(declare-const {name} {sort})")
        return name, sort
    
    def get_random_int_var(self):
        if self.int_vars:
            return random.choice(self.int_vars)
        return self.declare_int_var()
    
    def get_random_bool_var(self):
        if self.bool_vars:
            return random.choice(self.bool_vars)
        return self.declare_bool_var()
    
    def get_random_set_var(self):
        if self.set_vars:
            return random.choice(self.set_vars)
        return self.declare_set_var()
    
    def get_random_relation_var(self):
        if self.relation_vars:
            return random.choice(self.relation_vars)
        sorts = ['Int', 'Int']
        return self.declare_relation_var(sorts)
    
    def get_random_tuple_var(self):
        if self.tuple_vars:
            return random.choice(self.tuple_vars)
        sorts = ['Int', 'Int']
        return self.declare_tuple_var(sorts)

# ============================================================================
# Term Generator
# ============================================================================

class TermGenerator:
    def __init__(self, symbol_table, max_depth=5):
        self.symbol_table = symbol_table
        self.max_depth = max_depth
        
    def generate_int_term(self, depth=0):
        if depth >= self.max_depth:
            return str(random.randint(0, 10))
        
        choices = ['literal', 'var', 'arithmetic', 'cardinality']
        choice = random.choice(choices)
        
        if choice == 'literal':
            return str(random.randint(-5, 10))
        elif choice == 'var':
            return self.symbol_table.get_random_int_var()
        elif choice == 'arithmetic':
            op = random.choice(['+', '-', '*', 'div', 'mod'])
            if op == '-' and random.random() < 0.3:
                return f"(- {self.generate_int_term(depth+1)})"
            else:
                t1 = self.generate_int_term(depth+1)
                t2 = self.generate_int_term(depth+1)
                if random.random() < 0.3 and op in ['+', '*']:
                    t3 = self.generate_int_term(depth+1)
                    return f"({op} {t1} {t2} {t3})"
                return f"({op} {t1} {t2})"
        elif choice == 'cardinality':
            if random.random() < 0.5:
                set_term = self.generate_set_term(depth+1)
                return f"(set.card {set_term})"
            else:
                rel_term = self.generate_relation_term(depth+1)
                return f"(set.card {rel_term})"
        
        return str(random.randint(0, 10))
    
    def generate_set_term(self, depth=0):
        if depth >= self.max_depth:
            return "(as set.empty (Set Int))"
        
        choices = ['var', 'empty', 'universe', 'singleton', 'union', 'inter', 'minus', 'complement', 'insert']
        choice = random.choice(choices)
        
        if choice == 'var':
            name, _ = self.symbol_table.get_random_set_var()
            return name
        elif choice == 'empty':
            return "(as set.empty (Set Int))"
        elif choice == 'universe':
            return "(as set.universe (Set Int))"
        elif choice == 'singleton':
            int_term = self.generate_int_term(depth+1)
            return f"(set.singleton {int_term})"
        elif choice == 'union':
            s1 = self.generate_set_term(depth+1)
            s2 = self.generate_set_term(depth+1)
            return f"(set.union {s1} {s2})"
        elif choice == 'inter':
            s1 = self.generate_set_term(depth+1)
            s2 = self.generate_set_term(depth+1)
            return f"(set.inter {s1} {s2})"
        elif choice == 'minus':
            s1 = self.generate_set_term(depth+1)
            s2 = self.generate_set_term(depth+1)
            return f"(set.minus {s1} {s2})"
        elif choice == 'complement':
            s = self.generate_set_term(depth+1)
            return f"(set.complement {s})"
        elif choice == 'insert':
            int_term = self.generate_int_term(depth+1)
            set_term = self.generate_set_term(depth+1)
            return f"(set.insert {int_term} {set_term})"
        
        return "(as set.empty (Set Int))"
    
    def generate_tuple_term(self, depth=0):
        if depth >= self.max_depth:
            return "tuple.unit"
        
        choices = ['var', 'constructor', 'unit']
        choice = random.choice(choices)
        
        if choice == 'var':
            name, _ = self.symbol_table.get_random_tuple_var()
            return name
        elif choice == 'constructor':
            num_elems = random.randint(1, 3)
            elems = [self.generate_int_term(depth+1) for _ in range(num_elems)]
            return f"(tuple {' '.join(elems)})"
        elif choice == 'unit':
            return "tuple.unit"
        
        return "tuple.unit"
    
    def generate_relation_term(self, depth=0):
        if depth >= self.max_depth:
            return "(as set.empty (Relation Int Int))"
        
        choices = ['var', 'empty', 'singleton', 'union', 'inter', 'minus', 'transpose', 'join', 'product']
        choice = random.choice(choices)
        
        if choice == 'var':
            name, _ = self.symbol_table.get_random_relation_var()
            return name
        elif choice == 'empty':
            return "(as set.empty (Relation Int Int))"
        elif choice == 'singleton':
            tuple_term = self.generate_tuple_term(depth+1)
            return f"(set.singleton {tuple_term})"
        elif choice == 'union':
            r1 = self.generate_relation_term(depth+1)
            r2 = self.generate_relation_term(depth+1)
            return f"(set.union {r1} {r2})"
        elif choice == 'inter':
            r1 = self.generate_relation_term(depth+1)
            r2 = self.generate_relation_term(depth+1)
            return f"(set.inter {r1} {r2})"
        elif choice == 'minus':
            r1 = self.generate_relation_term(depth+1)
            r2 = self.generate_relation_term(depth+1)
            return f"(set.minus {r1} {r2})"
        elif choice == 'transpose':
            r = self.generate_relation_term(depth+1)
            return f"(rel.transpose {r})"
        elif choice == 'join':
            r1 = self.generate_relation_term(depth+1)
            r2 = self.generate_relation_term(depth+1)
            return f"(rel.join {r1} {r2})"
        elif choice == 'product':
            r1 = self.generate_relation_term(depth+1)
            r2 = self.generate_relation_term(depth+1)
            return f"(rel.product {r1} {r2})"
        
        return "(as set.empty (Relation Int Int))"
    
    def generate_bool_term(self, depth=0):
        if depth >= self.max_depth:
            return random.choice(['true', 'false'])
        
        choices = [
            'literal', 'var', 'set_member', 'set_subset', 'set_is_empty',
            'set_is_singleton', 'equality', 'int_comparison',
            'not', 'and', 'or', 'implies', 'ite'
        ]
        
        choice = random.choice(choices)
        
        if choice == 'literal':
            return random.choice(['true', 'false'])
        elif choice == 'var':
            return self.symbol_table.get_random_bool_var()
        elif choice == 'set_member':
            if random.random() < 0.5:
                int_term = self.generate_int_term(depth+1)
                set_term = self.generate_set_term(depth+1)
                return f"(set.member {int_term} {set_term})"
            else:
                tuple_term = self.generate_tuple_term(depth+1)
                rel_term = self.generate_relation_term(depth+1)
                return f"(set.member {tuple_term} {rel_term})"
        elif choice == 'set_subset':
            if random.random() < 0.5:
                s1 = self.generate_set_term(depth+1)
                s2 = self.generate_set_term(depth+1)
                return f"(set.subset {s1} {s2})"
            else:
                r1 = self.generate_relation_term(depth+1)
                r2 = self.generate_relation_term(depth+1)
                return f"(set.subset {r1} {r2})"
        elif choice == 'set_is_empty':
            if random.random() < 0.5:
                s = self.generate_set_term(depth+1)
                return f"(set.is_empty {s})"
            else:
                r = self.generate_relation_term(depth+1)
                return f"(set.is_empty {r})"
        elif choice == 'set_is_singleton':
            if random.random() < 0.5:
                s = self.generate_set_term(depth+1)
                return f"(set.is_singleton {s})"
            else:
                r = self.generate_relation_term(depth+1)
                return f"(set.is_singleton {r})"
        elif choice == 'equality':
            eq_type = random.choice(['set', 'relation', 'int', 'tuple'])
            if eq_type == 'set':
                s1 = self.generate_set_term(depth+1)
                s2 = self.generate_set_term(depth+1)
                return f"(= {s1} {s2})"
            elif eq_type == 'relation':
                r1 = self.generate_relation_term(depth+1)
                r2 = self.generate_relation_term(depth+1)
                return f"(= {r1} {r2})"
            elif eq_type == 'int':
                i1 = self.generate_int_term(depth+1)
                i2 = self.generate_int_term(depth+1)
                return f"(= {i1} {i2})"
            else:
                t1 = self.generate_tuple_term(depth+1)
                t2 = self.generate_tuple_term(depth+1)
                return f"(= {t1} {t2})"
        elif choice == 'int_comparison':
            op = random.choice(['<', '<=', '>', '>='])
            i1 = self.generate_int_term(depth+1)
            i2 = self.generate_int_term(depth+1)
            return f"({op} {i1} {i2})"
        elif choice == 'not':
            b = self.generate_bool_term(depth+1)
            return f"(not {b})"
        elif choice == 'and':
            b1 = self.generate_bool_term(depth+1)
            b2 = self.generate_bool_term(depth+1)
            if random.random() < 0.3:
                b3 = self.generate_bool_term(depth+1)
                return f"(and {b1} {b2} {b3})"
            return f"(and {b1} {b2})"
        elif choice == 'or':
            b1 = self.generate_bool_term(depth+1)
            b2 = self.generate_bool_term(depth+1)
            if random.random() < 0.3:
                b3 = self.generate_bool_term(depth+1)
                return f"(or {b1} {b2} {b3})"
            return f"(or {b1} {b2})"
        elif choice == 'implies':
            b1 = self.generate_bool_term(depth+1)
            b2 = self.generate_bool_term(depth+1)
            return f"(=> {b1} {b2})"
        elif choice == 'ite':
            cond = self.generate_bool_term(depth+1)
            then_b = self.generate_bool_term(depth+1)
            else_b = self.generate_bool_term(depth+1)
            return f"(ite {cond} {then_b} {else_b})"
        
        return 'true'

# ============================================================================
# Main Generator Function
# ============================================================================

def generate_setsandrelations_formula_with_decls():
    sort_manager = SortManager()
    symbol_table = SymbolTable(sort_manager)
    
    # Create some variables
    num_int_vars = random.randint(2, 5)
    num_bool_vars = random.randint(1, 3)
    num_set_vars = random.randint(1, 4)
    num_relation_vars = random.randint(1, 3)
    num_tuple_vars = random.randint(1, 3)
    
    for _ in range(num_int_vars):
        symbol_table.declare_int_var()
    
    for _ in range(num_bool_vars):
        symbol_table.declare_bool_var()
    
    for _ in range(num_set_vars):
        symbol_table.declare_set_var('Int')
    
    for _ in range(num_relation_vars):
        symbol_table.declare_relation_var(['Int', 'Int'])
    
    for _ in range(num_tuple_vars):
        symbol_table.declare_tuple_var(['Int', 'Int'])
    
    # Generate formula
    max_depth = random.randint(3, 6)
    term_generator = TermGenerator(symbol_table, max_depth)
    formula = term_generator.generate_bool_term(depth=0)
    
    # Build declarations string
    decls_str = '\n'.join(symbol_table.declarations)
    
    return decls_str, formula