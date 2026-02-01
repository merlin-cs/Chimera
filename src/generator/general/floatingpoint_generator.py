# complete Python module
import random
import string

# SMT-LIB keywords to avoid for generated names.
# This is not exhaustive but covers the most common ones.
SMT_KEYWORDS = {
    "abs", "and", "assert", "check-sat", "check-sat-assuming", "declare-const",
    "declare-fun", "declare-sort", "define-fun", "define-sort", "distinct",
    "echo", "exit", "exists", "false", "forall", "get-assertions", "get-assignment",
    "get-info", "get-model", "get-option", "get-proof", "get-unsat-core",
    "get-value", "ite", "let", "not", "or", "pop", "push", "reset", "set-info",
    "set-logic", "set-option", "true", "xor", "Real", "Int", "Bool", "Array",
    "BitVec", "FloatingPoint", "RoundingMode", "fp", "to_fp", "to_fp_unsigned",
    "fp.abs", "fp.add", "fp.div", "fp.eq", "fp.fma", "fp.geq", "fp.gt", "fp.isInfinite",
    "fp.isNaN", "fp.isNegative", "fp.isNormal", "fp.isPositive", "fp.isSubnormal",
    "fp.isZero", "fp.leq", "fp.lt", "fp.max", "fp.min", "fp.mul", "fp.neg", "fp.rem",
    "fp.roundToIntegral", "fp.sqrt", "fp.sub", "fp.to_sbv", "fp.to_ubv", "fp.to_real",
    "RNE", "RNA", "RTP", "RTN", "RTZ", "roundNearestTiesToEven",
    "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative",
    "roundTowardZero", "+oo", "-oo", "+zero", "-zero", "NaN",
    "bvadd", "bvmul", "bvand", "bvor", "concat", "extract"
}

# --- State Management Class ---

class GeneratorState:
    """Manages the state for a single formula generation run."""
    def __init__(self):
        self.max_depth = random.randint(3, 6)
        self.declarations = []
        self.used_names = set(SMT_KEYWORDS)
        self.symbol_table = {}  # sort -> [var_name, ...]

        # --- Sort Configuration ---
        # Standard FP sorts
        self.fp_sorts = [
            "(_ FloatingPoint 5 11)",  # Float16
            "(_ FloatingPoint 8 24)",  # Float32
            "(_ FloatingPoint 11 53)", # Float64
        ]
        # Add a random custom FP sort
        eb = random.randint(4, 12)
        sb = random.randint(8, 60)
        if eb > 1 and sb > 1:
            self.fp_sorts.append(f"(_ FloatingPoint {eb} {sb})")
        
        self.fp_sorts = list(set(self.fp_sorts)) # Ensure uniqueness

        # Derive BV sorts from FP sorts
        self.bv_sorts = []
        for fp_sort in self.fp_sorts:
            eb, sb = self._parse_fp_sort(fp_sort)
            self.bv_sorts.append(f"(_ BitVec {eb})")
            self.bv_sorts.append(f"(_ BitVec {sb})")
            self.bv_sorts.append(f"(_ BitVec {eb + sb})")
        # Add some other common/random bit-widths
        self.bv_sorts.extend([f"(_ BitVec {w})" for w in [1, 8, 16, 32, 64]])
        self.bv_sorts = list(set(self.bv_sorts)) # Ensure uniqueness

        self.all_sorts = (
            ["Bool", "Real", "RoundingMode"] + self.fp_sorts + self.bv_sorts
        )

    def _generate_name(self, prefix='v'):
        """Generates a new, unique, valid SMT-LIB symbol name."""
        while True:
            name = prefix + ''.join(random.choices(string.ascii_lowercase, k=random.randint(4, 8)))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _get_or_create_var(self, sort):
        """Gets an existing variable of a sort or creates a new one."""
        if sort not in self.symbol_table:
            self.symbol_table[sort] = []

        # 25% chance to create a new variable, 75% to reuse an existing one
        if not self.symbol_table[sort] or random.random() < 0.25:
            var_name = self._generate_name(prefix=self._get_sort_prefix(sort))
            self.declarations.append(f"(declare-const {var_name} {sort})")
            self.symbol_table[sort].append(var_name)
            return var_name
        
        return random.choice(self.symbol_table[sort])

    @staticmethod
    def _get_sort_prefix(sort):
        if "FloatingPoint" in sort: return "fp"
        if "BitVec" in sort: return "bv"
        if "RoundingMode" in sort: return "rm"
        if "Real" in sort: return "r"
        return "b"

    @staticmethod
    def _parse_fp_sort(sort_str):
        """Parses '(_ FloatingPoint eb sb)' into (eb, sb)."""
        parts = sort_str.replace("(", "").replace(")", "").split()
        return int(parts[2]), int(parts[3])

    @staticmethod
    def _parse_bv_sort(sort_str):
        """Parses '(_ BitVec m)' into m."""
        parts = sort_str.replace("(", "").replace(")", "").split()
        return int(parts[2])

# --- Helper Functions for Term Generation ---

def _generate_bool_term(state, depth):
    if depth <= 0:
        choices = ["var", "literal"]
        weights = [0.8, 0.2]
        choice = random.choices(choices, weights)[0]
        if choice == "var":
            return state._get_or_create_var("Bool")
        else:
            return random.choice(["true", "false"])

    # Production rules for <bool_term>
    productions = [
        "var", "literal", "not", "connective", "eq", "distinct", "ite",
        "fp_predicate_binary", "fp_predicate_unary"
    ]
    weights = [
        1, 1, 5, 8, 8, 4, 5, # Core
        10, # FP binary predicates
        8   # FP unary predicates
    ]
    choice = random.choices(productions, weights)[0]

    if choice == "var":
        return state._get_or_create_var("Bool")
    if choice == "literal":
        return random.choice(["true", "false"])
    if choice == "not":
        child = _generate_bool_term(state, depth - 1)
        return f"(not {child})"
    if choice == "connective":
        op = random.choice(["and", "or", "xor", "=>"])
        num_args = random.randint(2, 4)
        args = [_generate_bool_term(state, depth - 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    if choice == "eq" or choice == "distinct":
        # FIX: Use '=' for equality, not 'eq'.
        op = "=" if choice == "eq" else "distinct"
        # Pick a sort for the equality/disequality
        sort = random.choice(state.all_sorts)
        num_args = random.randint(2, 3)
        args = [_generate_term_of_sort(state, sort, depth - 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    if choice == "ite":
        cond = _generate_bool_term(state, depth - 1)
        t_branch = _generate_bool_term(state, depth - 1)
        f_branch = _generate_bool_term(state, depth - 1)
        return f"(ite {cond} {t_branch} {f_branch})"
    if choice == "fp_predicate_binary":
        op = random.choice(["fp.leq", "fp.lt", "fp.geq", "fp.gt", "fp.eq"])
        fp_sort = random.choice(state.fp_sorts)
        num_args = random.randint(2, 3)
        args = [_generate_fp_term(state, fp_sort, depth - 1) for _ in range(num_args)]
        return f"({op} {' '.join(args)})"
    if choice == "fp_predicate_unary":
        op = random.choice([
            "fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite",
            "fp.isNaN", "fp.isNegative", "fp.isPositive"
        ])
        fp_sort = random.choice(state.fp_sorts)
        arg = _generate_fp_term(state, fp_sort, depth - 1)
        return f"({op} {arg})"
    
    # Fallback
    return state._get_or_create_var("Bool")

def _generate_fp_term(state, sort, depth):
    eb, sb = state._parse_fp_sort(sort)

    if depth <= 0:
        choices = ["var", "const"]
        weights = [0.8, 0.2]
        choice = random.choices(choices, weights)[0]
        if choice == "var":
            return state._get_or_create_var(sort)
        else: # const
            const = random.choice(["+oo", "-oo", "+zero", "-zero", "NaN"])
            return f"(_ {const} {eb} {sb})"

    productions = [
        "var", "const", "unary_op", "binary_op_rm", "binary_op_no_rm", "fma",
        "sqrt_round", "conversion", "ite", "fp_constructor"
    ]
    weights = [
        2, 2, 6, 8, 6, 5, 5, 7, 5, 3
    ]
    choice = random.choices(productions, weights)[0]

    if choice == "var":
        return state._get_or_create_var(sort)
    if choice == "const":
        const = random.choice(["+oo", "-oo", "+zero", "-zero", "NaN"])
        return f"(_ {const} {eb} {sb})"
    if choice == "unary_op":
        op = random.choice(["fp.abs", "fp.neg"])
        arg = _generate_fp_term(state, sort, depth - 1)
        return f"({op} {arg})"
    if choice == "binary_op_rm":
        op = random.choice(["fp.add", "fp.sub", "fp.mul", "fp.div"])
        rm = _generate_rm_term(state, depth - 1)
        arg1 = _generate_fp_term(state, sort, depth - 1)
        arg2 = _generate_fp_term(state, sort, depth - 1)
        return f"({op} {rm} {arg1} {arg2})"
    if choice == "binary_op_no_rm":
        op = random.choice(["fp.rem", "fp.min", "fp.max"])
        arg1 = _generate_fp_term(state, sort, depth - 1)
        arg2 = _generate_fp_term(state, sort, depth - 1)
        return f"({op} {arg1} {arg2})"
    if choice == "fma":
        rm = _generate_rm_term(state, depth - 1)
        arg1 = _generate_fp_term(state, sort, depth - 1)
        arg2 = _generate_fp_term(state, sort, depth - 1)
        arg3 = _generate_fp_term(state, sort, depth - 1)
        return f"(fp.fma {rm} {arg1} {arg2} {arg3})"
    if choice == "sqrt_round":
        op = random.choice(["fp.sqrt", "fp.roundToIntegral"])
        rm = _generate_rm_term(state, depth - 1)
        arg = _generate_fp_term(state, sort, depth - 1)
        return f"({op} {rm} {arg})"
    if choice == "conversion":
        # From what sort are we converting?
        from_sort_type = random.choice(["fp", "real", "sbv", "ubv"])
        rm = _generate_rm_term(state, depth - 1)
        
        if from_sort_type == "fp":
            # to_fp from another fp
            other_fp_sort = random.choice([s for s in state.fp_sorts if s != sort] or [sort])
            arg = _generate_fp_term(state, other_fp_sort, depth - 1)
            return f"((_ to_fp {eb} {sb}) {rm} {arg})"
        elif from_sort_type == "real":
            arg = _generate_real_term(state, depth - 1)
            return f"((_ to_fp {eb} {sb}) {rm} {arg})"
        elif from_sort_type == "ubv":
            # to_fp_unsigned from bv
            bv_sort = random.choice(state.bv_sorts)
            arg = _generate_bv_term(state, bv_sort, depth - 1)
            return f"((_ to_fp_unsigned {eb} {sb}) {rm} {arg})"
        else: # "sbv"
            # to_fp from signed bv
            bv_sort = random.choice(state.bv_sorts)
            arg = _generate_bv_term(state, bv_sort, depth - 1)
            return f"((_ to_fp {eb} {sb}) {rm} {arg})"
    if choice == "ite":
        cond = _generate_bool_term(state, depth - 1)
        t_branch = _generate_fp_term(state, sort, depth - 1)
        f_branch = _generate_fp_term(state, sort, depth - 1)
        return f"(ite {cond} {t_branch} {f_branch})"
    if choice == "fp_constructor":
        # (fp <bv_term> <bv_term> <bv_term>)
        # Sorts must be (_ BitVec 1), (_ BitVec eb), (_ BitVec sb-1)
        sign_bv = _generate_bv_term(state, "(_ BitVec 1)", depth - 1)
        exp_bv = _generate_bv_term(state, f"(_ BitVec {eb})", depth - 1)
        sig_bv = _generate_bv_term(state, f"(_ BitVec {sb-1})", depth - 1)
        return f"(fp {sign_bv} {exp_bv} {sig_bv})"
        
    # Fallback
    return state._get_or_create_var(sort)

def _generate_rm_term(state, depth):
    if depth <= 0 or random.random() < 0.7: # High chance of being a literal
        return random.choice([
            "RNE", "RNA", "RTP", "RTN", "RTZ"
        ])

    productions = ["var", "ite"]
    weights = [3, 7]
    choice = random.choices(productions, weights)[0]
    
    if choice == "var":
        return state._get_or_create_var("RoundingMode")
    if choice == "ite":
        cond = _generate_bool_term(state, depth - 1)
        t_branch = _generate_rm_term(state, depth - 1)
        f_branch = _generate_rm_term(state, depth - 1)
        return f"(ite {cond} {t_branch} {f_branch})"

    # Fallback
    return "RNE"

def _generate_bv_term(state, sort, depth):
    m = state._parse_bv_sort(sort)

    if depth <= 0:
        choices = ["var", "literal"]
        weights = [0.6, 0.4]
        choice = random.choices(choices, weights)[0]
        if choice == "var":
            return state._get_or_create_var(sort)
        else: # literal
            # FIX: Always use binary format #b to guarantee correct bit-width `m`.
            # Hex format #x can only represent widths that are multiples of 4.
            return f"#b{''.join(random.choices('01', k=m))}"

    productions = ["var", "literal", "conversion", "ite"]
    weights = [3, 2, 8, 5]
    choice = random.choices(productions, weights)[0]

    if choice == "var":
        return state._get_or_create_var(sort)
    if choice == "literal":
        # FIX: Always use binary format #b to guarantee correct bit-width `m`.
        return f"#b{''.join(random.choices('01', k=m))}"
    if choice == "conversion":
        op = random.choice(["fp.to_ubv", "fp.to_sbv"])
        rm = _generate_rm_term(state, depth - 1)
        fp_sort = random.choice(state.fp_sorts)
        fp_arg = _generate_fp_term(state, fp_sort, depth - 1)
        return f"((_ {op} {m}) {rm} {fp_arg})"
    if choice == "ite":
        cond = _generate_bool_term(state, depth - 1)
        t_branch = _generate_bv_term(state, sort, depth - 1)
        f_branch = _generate_bv_term(state, sort, depth - 1)
        return f"(ite {cond} {t_branch} {f_branch})"

    # Fallback
    return state._get_or_create_var(sort)

def _generate_real_term(state, depth):
    if depth <= 0:
        choices = ["var", "literal"]
        weights = [0.7, 0.3]
        choice = random.choices(choices, weights)[0]
        if choice == "var":
            return state._get_or_create_var("Real")
        else: # literal
            sign = random.choice(["", "-"])
            i_part = random.randint(0, 1000)
            f_part = random.randint(0, 999)
            return f"{sign}{i_part}.{f_part}"

    productions = ["var", "literal", "conversion", "ite"]
    weights = [3, 2, 8, 5]
    choice = random.choices(productions, weights)[0]

    if choice == "var":
        return state._get_or_create_var("Real")
    if choice == "literal":
        sign = random.choice(["", "-"])
        i_part = random.randint(0, 1000)
        f_part = random.randint(0, 999)
        return f"{sign}{i_part}.{f_part}"
    if choice == "conversion":
        fp_sort = random.choice(state.fp_sorts)
        fp_arg = _generate_fp_term(state, fp_sort, depth - 1)
        return f"(fp.to_real {fp_arg})"
    if choice == "ite":
        cond = _generate_bool_term(state, depth - 1)
        t_branch = _generate_real_term(state, depth - 1)
        f_branch = _generate_real_term(state, depth - 1)
        return f"(ite {cond} {t_branch} {f_branch})"
    
    # Fallback
    return state._get_or_create_var("Real")

def _generate_term_of_sort(state, sort, depth):
    """Dispatcher to generate a term of a specific sort."""
    if sort == "Bool":
        return _generate_bool_term(state, depth)
    if "FloatingPoint" in sort:
        return _generate_fp_term(state, sort, depth)
    if "RoundingMode" in sort:
        return _generate_rm_term(state, depth)
    if "BitVec" in sort:
        return _generate_bv_term(state, sort, depth)
    if "Real" in sort:
        return _generate_real_term(state, depth)
    # Should not be reached
    raise ValueError(f"Unknown sort for generation: {sort}")

# --- Public API Function ---

def generate_floatingpoint_formula_with_decls():
    """
    Generates a random, well-typed SMT-LIB2 formula for the FloatingPoint theory.

    Returns:
        A tuple (decls, formula) where:
        - decls (str): SMT-LIB2 declarations for all symbols used.
        - formula (str): A single SMT-LIB2 Boolean term.
    """
    state = GeneratorState()
    
    # Pre-populate with a few variables of each sort to ensure generation doesn't fail
    # on the first try and to increase diversity.
    num_initial_vars = random.randint(1, 3)
    for sort in state.all_sorts:
        for _ in range(num_initial_vars):
            state._get_or_create_var(sort)

    formula_str = _generate_bool_term(state, state.max_depth)
    
    # Sort declarations for deterministic output (easier debugging)
    decls_str = "\n".join(sorted(state.declarations))

    return decls_str, formula_str