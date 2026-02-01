# complete Python module
import random
import string
from collections import defaultdict

# SMT-LIB keywords to avoid for generated symbol names.
_SMT_KEYWORDS = {
    "!", "_", "as", "assert", "check-sat", "check-sat-assuming", "declare-const",
    "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort",
    "define-fun", "define-fun-rec", "define-funs-rec", "define-sort", "echo",
    "exit", "get-assertions", "get-assignment", "get-info", "get-model",
    "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core",
    "get-value", "pop", "push", "reset", "reset-assertions", "set-info",
    "set-logic", "set-option", "and", "or", "not", "=>", "xor", "ite", "true",
    "false", "distinct", "let", "forall", "exists", "match", "par", "continued-execution",
    "error", "immediate-exit", "incomplete", "logic", "memout", "sat", "success",
    "theory", "unknown", "unsupported", "unsat", "BINARY", "DECIMAL", "HEXADECIMAL",
    "NUMERAL", "STRING", "tuple", "is", "update", "select", "project", "UnitTuple", "Tuple"
}

# --- Symbol Name Generation ---

def _generate_name(used_names, min_len=5, max_len=8):
    """Generates a new random name that is not a keyword or already used."""
    while True:
        length = random.randint(min_len, max_len)
        name = ''.join(random.choice(string.ascii_lowercase) for _ in range(length))
        if name not in used_names:
            used_names.add(name)
            return name

# --- Sort and Datatype Structure Representation ---

class Sort:
    """Base class for SMT-LIB sorts."""
    def __str__(self):
        raise NotImplementedError

    def __eq__(self, other):
        return isinstance(other, self.__class__) and str(self) == str(other)

    def __hash__(self):
        return hash(str(self))

class SimpleSort(Sort):
    """A simple, non-parametric sort like 'Bool', 'Int', or a user-defined one."""
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name
    def __eq__(self, other):
        return isinstance(other, SimpleSort) and self.name == other.name

class TupleSort(Sort):
    """A tuple sort, e.g., (Tuple Int String)."""
    def __init__(self, component_sorts):
        self.components = tuple(component_sorts)
    def __str__(self):
        if not self.components:
            return "UnitTuple"
        return f"(Tuple {' '.join(map(str, self.components))})"
    def __eq__(self, other):
        return isinstance(other, TupleSort) and self.components == other.components

class DatatypeSort(Sort):
    """An instantiated datatype sort, e.g., (list Int)."""
    def __init__(self, basename, params=None):
        self.basename = basename
        self.params = tuple(params) if params else tuple()
    def __str__(self):
        if not self.params:
            return self.basename
        return f"({self.basename} {' '.join(map(str, self.params))})"
    def __eq__(self, other):
        return isinstance(other, DatatypeSort) and self.basename == other.basename and self.params == other.params

class Selector:
    """Represents a selector in a datatype constructor."""
    def __init__(self, name, sort):
        self.name = name
        self.sort = sort
    def __str__(self):
        return f"({self.name} {self.sort})"

class Constructor:
    """Represents a constructor in a datatype definition."""
    def __init__(self, name, selectors):
        self.name = name
        self.selectors = selectors
    def __str__(self):
        if not self.selectors:
            return self.name
        return f"({self.name} {' '.join(map(str, self.selectors))})"

class DatatypeDef:
    """Represents a complete datatype definition (parametric or not)."""
    def __init__(self, name, params, constructors):
        self.name = name
        self.params = params  # List of string names for type parameters
        self.constructors = constructors

# --- Main Generation Context ---

class GenerationContext:
    """Holds the state for a single formula generation process."""
    def __init__(self):
        self.used_names = set(_SMT_KEYWORDS)
        self.declarations = []
        self.max_depth = random.randint(4, 6)

        # Datatype definitions
        self.datatype_defs = {}  # name -> DatatypeDef

        # All available concrete sorts (instantiated)
        self.sorts = {}  # str_repr -> Sort object

        # Available variables per sort
        self.variables = defaultdict(list)

        # Other theory functions: name -> (arg_sorts, ret_sort)
        self.other_funcs = {}

        self._init_builtins()

    def get_new_name(self):
        return _generate_name(self.used_names)

    def _init_builtins(self):
        """Initializes built-in sorts and functions for diversity."""
        # Sorts
        for s in [SimpleSort("Bool"), SimpleSort("Int"), SimpleSort("String")]:
            self.sorts[str(s)] = s

        # Int functions
        int_s = self.sorts["Int"]
        bool_s = self.sorts["Bool"]
        self.other_funcs['+'] = ([int_s, int_s], int_s)
        self.other_funcs['-'] = ([int_s, int_s], int_s)
        self.other_funcs['*'] = ([int_s, int_s], int_s)
        self.other_funcs['<'] = ([int_s, int_s], bool_s)
        self.other_funcs['<='] = ([int_s, int_s], bool_s)
        self.other_funcs['>'] = ([int_s, int_s], bool_s)
        self.other_funcs['>='] = ([int_s, int_s], bool_s)

        # String functions
        str_s = self.sorts["String"]
        self.other_funcs['str.++'] = ([str_s, str_s], str_s)
        self.other_funcs['str.contains'] = ([str_s, str_s], bool_s)
        self.other_funcs['str.prefixof'] = ([str_s, str_s], bool_s)

    def get_sorts_by_type(self, sort_type):
        return [s for s in self.sorts.values() if isinstance(s, sort_type)]

    def get_random_sort(self, allow_bool=True):
        """Gets a random sort, optionally excluding Bool."""
        sort_list = list(self.sorts.values())
        if not allow_bool:
            sort_list = [s for s in sort_list if str(s) != "Bool"]
        if not sort_list:
            return self.sorts["Int"] # Fallback
        return random.choice(sort_list)

    def get_ambiguous_nullary_constructors(self):
        """Finds nullary constructors defined in more than one datatype."""
        counts = defaultdict(int)
        for dt_def in self.datatype_defs.values():
            for constr in dt_def.constructors:
                if not constr.selectors:
                    counts[constr.name] += 1
        return {name for name, count in counts.items() if count > 1}

# --- Core Formula Generator ---

class FormulaGenerator:
    """Implements the CFG-based generation logic."""

    def __init__(self, context):
        self.ctx = context

    def _create_datatype_definitions(self):
        """Generates random datatype definitions and adds them to the context."""
        num_datatypes = random.randint(1, 3)
        datatype_names = [self.ctx.get_new_name() for _ in range(num_datatypes)]
        param_counts = [random.choices([0, 1, 2], [0.6, 0.3, 0.1])[0] for _ in range(num_datatypes)]

        # Phase 1: Create skeletons
        for i in range(num_datatypes):
            name = datatype_names[i]
            params = [self.ctx.get_new_name() for _ in range(param_counts[i])]
            self.ctx.datatype_defs[name] = DatatypeDef(name, params, [])

        # Phase 2: Populate constructors (allows mutual recursion)
        for name in datatype_names:
            dt_def = self.ctx.datatype_defs[name]
            num_constructors = random.randint(1, 3)
            constructors = []
            
            # Designate a constructor to be non-self-recursive to ensure well-foundedness
            base_case_constr_idx = random.randrange(num_constructors)

            for i in range(num_constructors):
                constr_name = self.ctx.get_new_name()
                num_selectors = random.randint(0, 3)
                selectors = []
                
                is_base_case_constr = (i == base_case_constr_idx)

                for _ in range(num_selectors):
                    sel_name = self.ctx.get_new_name()
                    
                    all_sort_choices = list(self.ctx.datatype_defs.keys()) + ["Int", "String", "Bool"] + dt_def.params
                    
                    # For the base case constructor, prevent direct self-recursion.
                    if is_base_case_constr:
                        choices = [s for s in all_sort_choices if s != name]
                    else:
                        choices = all_sort_choices
                    
                    if not choices: # Safeguard
                        sort_name = "Int"
                    else:
                        sort_name = random.choice(choices)
                    
                    if sort_name in dt_def.params:
                        sel_sort = SimpleSort(sort_name)
                    elif sort_name in self.ctx.datatype_defs:
                        target_dt = self.ctx.datatype_defs[sort_name]
                        if target_dt.params:
                            param_map = [self._pick_sort_for_param(dt_def.params) for _ in target_dt.params]
                            sel_sort = DatatypeSort(target_dt.name, param_map)
                        else:
                            sel_sort = DatatypeSort(target_dt.name)
                    else: # Base sort
                        sel_sort = self.ctx.sorts[sort_name]
                    selectors.append(Selector(sel_name, sel_sort))
                constructors.append(Constructor(constr_name, selectors))
            dt_def.constructors = constructors
        
        if not datatype_names: return

        # Build (declare-datatypes) command
        dt_decls = []
        dt_defs_str = []
        for name in datatype_names:
            dt_def = self.ctx.datatype_defs[name]
            dt_decls.append(f"({name} {len(dt_def.params)})")
            constr_strs = [str(c) for c in dt_def.constructors]
            dt_defs_str.append(f"({' '.join(constr_strs)})")
        
        self.ctx.declarations.append(f"(declare-datatypes ({' '.join(dt_decls)}) ({' '.join(dt_defs_str)}))")

    def _pick_sort_for_param(self, available_params):
        """Picks a concrete sort for instantiating a type parameter."""
        choices = ["Int", "String"] + list(available_params)
        choice = random.choice(choices)
        if choice in available_params:
            return SimpleSort(choice) # Still a parameter, will be substituted later
        return self.ctx.sorts[choice]

    def _instantiate_parametric_datatypes(self):
        """Creates concrete datatype sorts from parametric definitions."""
        for dt_def in self.ctx.datatype_defs.values():
            if not dt_def.params:
                sort = DatatypeSort(dt_def.name)
                self.ctx.sorts[str(sort)] = sort
            else:
                for _ in range(random.randint(1, 2)):
                    param_map = [self.ctx.get_random_sort() for _ in dt_def.params]
                    sort = DatatypeSort(dt_def.name, param_map)
                    self.ctx.sorts[str(sort)] = sort

        for _ in range(random.randint(1, 3)):
            num_components = random.randint(0, 4)
            components = [self.ctx.get_random_sort() for _ in range(num_components)]
            sort = TupleSort(components)
            self.ctx.sorts[str(sort)] = sort

    def _declare_variables(self):
        """Declares variables for all available concrete sorts."""
        for sort_str, sort_obj in self.ctx.sorts.items():
            num_vars = random.randint(1, 3)
            for _ in range(num_vars):
                var_name = self.ctx.get_new_name()
                self.ctx.declarations.append(f"(declare-const {var_name} {sort_str})")
                self.ctx.variables[sort_str].append(var_name)

    def _get_term_of_sort(self, depth, target_sort):
        """Main recursive term generation function."""
        # Delegate boolean generation to its own specialized function
        if str(target_sort) == "Bool":
            return self._generate_boolean_term(depth)

        if depth >= self.ctx.max_depth:
            if self.ctx.variables[str(target_sort)]:
                return random.choice(self.ctx.variables[str(target_sort)])
            return None

        options, weights = [], []

        if self.ctx.variables[str(target_sort)]:
            options.append("variable"); weights.append(30)
        
        options.append("ite"); weights.append(15)

        if isinstance(target_sort, DatatypeSort):
            options.extend(["constructor_app", "updater_app"]); weights.extend([40, 10])
        elif isinstance(target_sort, TupleSort):
            if str(target_sort) == "UnitTuple":
                 options.append("unit_tuple"); weights.append(50)
            else:
                options.extend(["tuple_constructor", "tuple_updater"]); weights.extend([40, 10])
        
        funcs_returning_sort = [name for name, sig in self.ctx.other_funcs.items() if sig[1] == target_sort]
        if funcs_returning_sort:
            options.append("other_func"); weights.append(15)
        
        options.append("selector_app"); weights.append(10)
        options.extend(["tuple_selector", "tuple_projector"]); weights.extend([5, 5])
        
        if not options: return None

        random_productions = random.choices(options, weights, k=len(options))
        for choice in set(random_productions):
            term = None
            if choice == "variable":
                term = random.choice(self.ctx.variables[str(target_sort)])
            elif choice == "ite":
                term = self._generate_ite(depth + 1, target_sort)
            elif choice == "constructor_app":
                term = self._generate_constructor_app(depth + 1, target_sort)
            elif choice == "updater_app":
                term = self._generate_updater_app(depth + 1, target_sort)
            elif choice == "tuple_constructor":
                term = self._generate_tuple_constructor(depth + 1, target_sort)
            elif choice == "unit_tuple":
                term = "tuple.unit"
            elif choice == "tuple_updater":
                term = self._generate_tuple_updater(depth + 1, target_sort)
            elif choice == "other_func":
                term = self._generate_other_func_app(depth + 1, target_sort, funcs_returning_sort)
            elif choice == "selector_app":
                term = self._generate_selector_app(depth + 1, target_sort)
            elif choice == "tuple_selector":
                term = self._generate_tuple_selector(depth + 1, target_sort)
            elif choice == "tuple_projector":
                term = self._generate_tuple_projector(depth + 1, target_sort)

            if term is not None:
                return term
        
        if self.ctx.variables[str(target_sort)]:
            return random.choice(self.ctx.variables[str(target_sort)])
        
        return None

    def _generate_boolean_term(self, depth):
        """Generates a term of sort Bool."""
        if depth >= self.ctx.max_depth:
            bool_vars = self.ctx.variables["Bool"]
            choices = ["true", "false"] + (bool_vars if bool_vars else [])
            return random.choice(choices)

        options, weights = [], []
        options.extend(["tester", "equality", "distinct", "not", "nary_logic", "ite", "other_bool_func"])
        weights.extend([15, 20, 5, 10, 25, 10, 5])
        if self.ctx.variables["Bool"]:
            options.append("variable"); weights.append(10)

        random_productions = random.choices(options, weights, k=len(options))
        for choice in set(random_productions):
            term = None
            if choice == "tester":
                term = self._generate_tester_app(depth + 1)
            elif choice == "equality":
                s = self.ctx.get_random_sort()
                t1 = self._get_term_of_sort(depth + 1, s)
                t2 = self._get_term_of_sort(depth + 1, s)
                if t1 and t2: term = f"(= {t1} {t2})"
            elif choice == "distinct":
                s = self.ctx.get_random_sort()
                num_terms = random.randint(2, 4)
                terms = [self._get_term_of_sort(depth + 1, s) for _ in range(num_terms)]
                if all(terms): term = f"(distinct {' '.join(terms)})"
            elif choice == "not":
                sub = self._generate_boolean_term(depth + 1)
                if sub: term = f"(not {sub})"
            elif choice == "nary_logic":
                op = random.choice(["and", "or", "=>", "xor"])
                # Correction: Restrict '=>' and 'xor' to binary form for robustness,
                # as n-ary usage can be tricky and lead to parser errors, even if
                # the standard allows chaining.
                if op in ["=>", "xor"]:
                    num_terms = 2
                else:
                    num_terms = random.randint(2, 4)
                terms = [self._generate_boolean_term(depth + 1) for _ in range(num_terms)]
                if all(terms): term = f"({op} {' '.join(terms)})"
            elif choice == "ite":
                term = self._generate_ite(depth + 1, self.ctx.sorts["Bool"])
            elif choice == "variable":
                if self.ctx.variables["Bool"]:
                    term = random.choice(self.ctx.variables["Bool"])
            elif choice == "other_bool_func":
                bool_funcs = [name for name, sig in self.ctx.other_funcs.items() if str(sig[1]) == "Bool"]
                if bool_funcs:
                    term = self._generate_other_func_app(depth + 1, self.ctx.sorts["Bool"], bool_funcs)
            
            if term is not None:
                return term
        
        return random.choice(["true", "false"])

    def _generate_constructor_app(self, depth, target_sort):
        """Generates a constructor application, e.g., (cons h t)."""
        dt_def = self.ctx.datatype_defs.get(target_sort.basename)
        if not dt_def or not dt_def.constructors: return None

        constr = random.choice(dt_def.constructors)
        
        param_map = dict(zip(dt_def.params, target_sort.params))
        
        arg_terms = []
        for selector in constr.selectors:
            # This substitution logic is fragile and a common source of errors.
            # A more robust solution would involve recursive substitution on Sort objects.
            sel_sort_str = str(selector.sort)
            for p_name, p_sort in param_map.items():
                # This simple string replacement can fail on complex nested sorts.
                # E.g. replacing T in (pair T (list T))
                # The logic here tries to handle basic cases.
                sel_sort_str = sel_sort_str.replace(f"({p_name})", f"({p_sort})")
                sel_sort_str = sel_sort_str.replace(f" {p_name} ", f" {p_sort} ")
                sel_sort_str = sel_sort_str.replace(f"({p_name} ", f"({p_sort} ")
                sel_sort_str = sel_sort_str.replace(f" {p_name})", f" {p_sort})")
                if sel_sort_str == p_name: sel_sort_str = str(p_sort)

            actual_sort = self.ctx.sorts.get(sel_sort_str)
            if not actual_sort: return None

            arg = self._get_term_of_sort(depth + 1, actual_sort)
            if arg is None: return None
            arg_terms.append(arg)
        
        # A nullary constructor (no arguments) from a parametric datatype is ambiguous
        # by itself (e.g., 'nil'). It must be qualified with its concrete sort,
        # e.g., '(as nil (List Int))'. The same applies to nullary constructors
        # that are ambiguous (used in multiple datatypes).
        if not arg_terms:
            is_parametric = bool(dt_def.params)
            is_ambiguous = constr.name in self.ctx.get_ambiguous_nullary_constructors()
            if is_parametric or is_ambiguous:
                return f"(as {constr.name} {target_sort})"
            else: # Non-parametric, non-ambiguous nullary constructor is just its name.
                return constr.name

        return f"({constr.name} {' '.join(arg_terms)})"

    def _generate_tester_app(self, depth):
        """Generates a tester application, e.g., ((_ is cons) l)."""
        dt_sorts = [s for s in self.ctx.get_sorts_by_type(DatatypeSort) if self.ctx.variables[str(s)]]
        if not dt_sorts: return None
        
        sort_obj = random.choice(dt_sorts)
        dt_def = self.ctx.datatype_defs[sort_obj.basename]
        if not dt_def.constructors: return None
        
        constructor = random.choice(dt_def.constructors)
        term_to_test = self._get_term_of_sort(depth + 1, sort_obj)
        if term_to_test is None: return None

        return f"((_ is {constructor.name}) {term_to_test})"

    def _generate_selector_app(self, depth, target_sort):
        """Generates a selector application, e.g., (head l)."""
        possible_selectors = []
        for dt_def in self.ctx.datatype_defs.values():
            for s_inst in self.ctx.get_sorts_by_type(DatatypeSort):
                if s_inst.basename != dt_def.name: continue
                param_map = dict(zip(dt_def.params, s_inst.params))
                for constr in dt_def.constructors:
                    for sel in constr.selectors:
                        sel_sort_str = str(sel.sort)
                        for p_name, p_sort in param_map.items():
                            sel_sort_str = sel_sort_str.replace(f"({p_name})", f"({p_sort})")
                            sel_sort_str = sel_sort_str.replace(f" {p_name} ", f" {p_sort} ")
                            sel_sort_str = sel_sort_str.replace(f"({p_name} ", f"({p_sort} ")
                            sel_sort_str = sel_sort_str.replace(f" {p_name})", f" {p_sort})")
                            if sel_sort_str == p_name: sel_sort_str = str(p_sort)
                        
                        actual_sel_sort = self.ctx.sorts.get(sel_sort_str)
                        if actual_sel_sort == target_sort:
                            possible_selectors.append((sel, s_inst))

        if not possible_selectors: return None
        
        selector, parent_sort = random.choice(possible_selectors)
        
        parent_term = self._get_term_of_sort(depth + 1, parent_sort)
        if parent_term is None: return None
        
        return f"({selector.name} {parent_term})"

    def _generate_updater_app(self, depth, target_sort):
        """Generates ((_ update sel) term value)."""
        dt_def = self.ctx.datatype_defs.get(target_sort.basename)
        if not dt_def: return None
        
        all_selectors = [sel for constr in dt_def.constructors for sel in constr.selectors]
        if not all_selectors: return None
        
        selector = random.choice(all_selectors)
        
        param_map = dict(zip(dt_def.params, target_sort.params))
        sel_sort_str = str(selector.sort)
        for p_name, p_sort in param_map.items():
            sel_sort_str = sel_sort_str.replace(f"({p_name})", f"({p_sort})")
            sel_sort_str = sel_sort_str.replace(f" {p_name} ", f" {p_sort} ")
            sel_sort_str = sel_sort_str.replace(f"({p_name} ", f"({p_sort} ")
            sel_sort_str = sel_sort_str.replace(f" {p_name})", f" {p_sort})")
            if sel_sort_str == p_name: sel_sort_str = str(p_sort)

        sel_sort = self.ctx.sorts.get(sel_sort_str)
        if not sel_sort: return None
        
        dt_term = self._get_term_of_sort(depth + 1, target_sort)
        new_val_term = self._get_term_of_sort(depth + 1, sel_sort)
        
        if dt_term is None or new_val_term is None: return None
        
        return f"((_ update {selector.name}) {dt_term} {new_val_term})"
    
    def _generate_tuple_constructor(self, depth, target_sort):
        args = []
        for comp_sort in target_sort.components:
            arg = self._get_term_of_sort(depth + 1, comp_sort)
            if arg is None: return None
            args.append(arg)
        return f"(tuple {' '.join(args)})"

    def _generate_tuple_selector(self, depth, target_sort):
        possible_parents = []
        for sort_obj in self.ctx.get_sorts_by_type(TupleSort):
            if not self.ctx.variables[str(sort_obj)]: continue
            for i, comp_sort in enumerate(sort_obj.components):
                if comp_sort == target_sort:
                    possible_parents.append((sort_obj, i))
        
        if not possible_parents: return None
        
        parent_sort, index = random.choice(possible_parents)
        parent_term = self._get_term_of_sort(depth + 1, parent_sort)
        if parent_term is None: return None
        
        return f"((_ tuple.select {index}) {parent_term})"

    def _generate_tuple_updater(self, depth, target_sort):
        if not target_sort.components: return None

        index = random.randrange(len(target_sort.components))
        update_sort = target_sort.components[index]
        
        parent_term = self._get_term_of_sort(depth + 1, target_sort)
        update_val = self._get_term_of_sort(depth + 1, update_sort)
        
        if parent_term is None or update_val is None: return None
        
        return f"((_ tuple.update {index}) {parent_term} {update_val})"

    def _generate_tuple_projector(self, depth, target_sort):
        if not isinstance(target_sort, TupleSort): return None
        
        possible_parents = []
        for sort_obj in self.ctx.get_sorts_by_type(TupleSort):
            if len(sort_obj.components) > len(target_sort.components) and self.ctx.variables[str(sort_obj)]:
                 possible_parents.append(sort_obj)
        
        if not possible_parents: return None
        parent_sort = random.choice(possible_parents)
        
        indices = []
        target_comps = list(target_sort.components)
        parent_comps = list(parent_sort.components)
        
        # This is a greedy match, might not be optimal but is simple
        i = 0
        while i < len(parent_comps) and target_comps:
            if parent_comps[i] == target_comps[0]:
                indices.append(str(i))
                target_comps.pop(0)
            i += 1

        if not indices or target_comps: return None
        
        parent_term = self._get_term_of_sort(depth + 1, parent_sort)
        if parent_term is None: return None
        
        return f"((_ tuple.project {' '.join(indices)}) {parent_term})"

    def _generate_other_func_app(self, depth, target_sort, func_names):
        func_name = random.choice(func_names)
        arg_sorts, _ = self.ctx.other_funcs[func_name]
        
        args = []
        for arg_sort in arg_sorts:
            arg = self._get_term_of_sort(depth + 1, arg_sort)
            if arg is None: return None
            args.append(arg)
        
        if str(target_sort) == "Int" and random.random() < 0.2:
             return str(random.randint(-100, 100))
             
        return f"({func_name} {' '.join(args)})"

    def _generate_ite(self, depth, target_sort):
        cond = self._generate_boolean_term(depth + 1)
        then_b = self._get_term_of_sort(depth + 1, target_sort)
        else_b = self._get_term_of_sort(depth + 1, target_sort)
        if cond and then_b and else_b:
            return f"(ite {cond} {then_b} {else_b})"
        return None

# --- Public API Function ---

def generate_datatypes_formula_with_decls():
    """
    Generates a random SMT-LIB2 formula with datatypes and returns declarations and the formula.

    Returns:
        tuple[str, str]: A tuple containing the SMT-LIB declarations and the formula term.
    """
    try:
        context = GenerationContext()
        generator = FormulaGenerator(context)

        generator._create_datatype_definitions()
        generator._instantiate_parametric_datatypes()
        generator._declare_variables()

        formula = generator._generate_boolean_term(0)

        if formula is None:
            formula = "true"

        decls_str = "\n".join(context.declarations)
        return decls_str, formula
    except (IndexError, RecursionError, ValueError):
        # Catch potential errors from random choices on empty lists or deep recursion
        # and return a trivial valid formula.
        return "(declare-const x Bool)", "x"