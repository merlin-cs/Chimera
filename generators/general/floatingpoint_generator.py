import random

# Reserved SMT-LIB keywords to avoid
RESERVED_KEYWORDS = {
    'and', 'or', 'not', 'ite', 'true', 'false', 'exists', 'forall', 'let',
    'par', 'as', 'assert', 'check-sat', 'declare-fun', 'declare-const',
    'define-fun', 'get-model', 'set-logic', 'set-option', 'fp', 'xor',
    'distinct', 'RNE', 'RNA', 'RTP', 'RTN', 'RTZ', 'roundNearestTiesToEven',
    'roundNearestTiesToAway', 'roundTowardPositive', 'roundTowardNegative',
    'roundTowardZero', 'Bool', 'Float', 'FloatingPoint', 'BitVec', 'Real',
    'Int', 'Array'
}

def generate_random_name(min_len=5, max_len=12):
    """Generate a random lowercase name that is not a reserved keyword."""
    while True:
        length = random.randint(min_len, max_len)
        name = ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))
        if name not in RESERVED_KEYWORDS:
            return name

class FormulaGenerator:
    def __init__(self):
        self.fp_vars = {}  # (eb, sb) -> [var_names]
        self.bool_vars = []
        self.bv_vars = {}  # width -> [var_names]
        self.real_vars = []
        self.rm_vars = []
        self.decls = []
        self.max_depth = 5
        self.fp_sorts = [(5, 11), (8, 24), (11, 53)]  # half, single, double
        
    def add_fp_var(self, eb=None, sb=None):
        if eb is None or sb is None:
            eb, sb = random.choice(self.fp_sorts)
        name = generate_random_name()
        key = (eb, sb)
        if key not in self.fp_vars:
            self.fp_vars[key] = []
        self.fp_vars[key].append(name)
        self.decls.append(f"(declare-const {name} (_ FloatingPoint {eb} {sb}))")
        return name, eb, sb
    
    def add_bool_var(self):
        name = generate_random_name()
        self.bool_vars.append(name)
        self.decls.append(f"(declare-const {name} Bool)")
        return name
    
    def add_bv_var(self, width):
        name = generate_random_name()
        if width not in self.bv_vars:
            self.bv_vars[width] = []
        self.bv_vars[width].append(name)
        self.decls.append(f"(declare-const {name} (_ BitVec {width}))")
        return name
    
    def add_real_var(self):
        name = generate_random_name()
        self.real_vars.append(name)
        self.decls.append(f"(declare-const {name} Real)")
        return name
    
    def add_rm_var(self):
        name = generate_random_name()
        self.rm_vars.append(name)
        self.decls.append(f"(declare-const {name} RoundingMode)")
        return name
    
    def get_or_create_fp_var(self, eb=None, sb=None):
        if eb is None or sb is None:
            eb, sb = random.choice(self.fp_sorts)
        
        key = (eb, sb)
        if key not in self.fp_vars or not self.fp_vars[key] or random.random() < 0.3:
            return self.add_fp_var(eb, sb)
        return random.choice(self.fp_vars[key]), eb, sb
    
    def get_or_create_bool_var(self):
        if not self.bool_vars or random.random() < 0.3:
            return self.add_bool_var()
        return random.choice(self.bool_vars)
    
    def get_or_create_bv_var(self, width):
        if width not in self.bv_vars or not self.bv_vars[width] or random.random() < 0.3:
            return self.add_bv_var(width)
        return random.choice(self.bv_vars[width])
    
    def get_or_create_real_var(self):
        if not self.real_vars or random.random() < 0.3:
            return self.add_real_var()
        return random.choice(self.real_vars)
    
    def get_or_create_rm_var(self):
        if not self.rm_vars or random.random() < 0.3:
            return self.add_rm_var()
        return random.choice(self.rm_vars)
    
    def gen_rounding_mode(self):
        modes = ['RNE', 'RNA', 'RTP', 'RTN', 'RTZ']
        if self.rm_vars and random.random() < 0.2:
            return random.choice(self.rm_vars)
        return random.choice(modes)
    
    def gen_bv_literal(self, width):
        val = random.randint(0, (1 << width) - 1)
        return f"#b{bin(val)[2:].zfill(width)}"
    
    def gen_bv_term(self, width, depth=0):
        if depth > 2 or random.random() < 0.5:
            return self.gen_bv_literal(width)
        return self.get_or_create_bv_var(width)
    
    def gen_bv1_term(self, depth=0):
        choices = ['#b0', '#b1']
        if self.bv_vars.get(1) and random.random() < 0.2:
            choices.append(self.get_or_create_bv_var(1))
        return random.choice(choices)
    
    def gen_real_literal(self):
        if random.random() < 0.5:
            return str(random.randint(0, 100))
        else:
            num = random.randint(1, 100)
            denom = random.randint(1, 100)
            return f"{num}.{denom}"
    
    def gen_real_term(self, depth=0):
        if depth > 2:
            return self.gen_real_literal()
        
        choices = ['literal', 'variable']
        if self.fp_vars:
            choices.extend(['fp_to_real', 'division', 'negation'])
        
        choice = random.choice(choices)
        
        if choice == 'literal':
            return self.gen_real_literal()
        elif choice == 'variable':
            return self.get_or_create_real_var()
        elif choice == 'fp_to_real':
            fp, _, _ = self.gen_fp_term(depth + 1)
            return f"(fp.to_real {fp})"
        elif choice == 'division':
            n1 = random.randint(1, 100)
            n2 = random.randint(1, 100)
            return f"(/ {n1} {n2})"
        elif choice == 'negation':
            rt = self.gen_real_term(depth + 1)
            return f"(- {rt})"
        
        return self.gen_real_literal()
    
    def gen_fp_literal(self, eb, sb):
        sign = self.gen_bv1_term()
        exp = self.gen_bv_term(eb)
        sig = self.gen_bv_term(sb - 1)
        return f"(fp {sign} {exp} {sig})"
    
    def gen_fp_value(self, eb, sb, depth=0):
        choice = random.choice(['literal', 'infinity', 'zero', 'nan'])
        
        if choice == 'literal':
            return self.gen_fp_literal(eb, sb)
        elif choice == 'infinity':
            sign = random.choice(['+', '-'])
            return f"(_ {sign}oo {eb} {sb})"
        elif choice == 'zero':
            sign = random.choice(['+', '-'])
            return f"(_ {sign}zero {eb} {sb})"
        else:  # nan
            return f"(_ NaN {eb} {sb})"
    
    def gen_fp_term(self, depth=0, eb=None, sb=None):
        """Generate a floating-point term with specific sort (eb, sb)."""
        if eb is None or sb is None:
            eb, sb = random.choice(self.fp_sorts)
        
        if depth >= self.max_depth:
            name, _, _ = self.get_or_create_fp_var(eb, sb)
            return name, eb, sb
        
        choices = ['value', 'variable', 'unary_op', 'binary_op', 'ternary_op']
        if depth < self.max_depth - 1:
            choices.extend(['conversion', 'ite'])
        
        choice = random.choice(choices)
        
        if choice == 'value':
            return self.gen_fp_value(eb, sb, depth), eb, sb
        elif choice == 'variable':
            name, _, _ = self.get_or_create_fp_var(eb, sb)
            return name, eb, sb
        elif choice == 'unary_op':
            return self.gen_fp_unary_op(depth, eb, sb)
        elif choice == 'binary_op':
            return self.gen_fp_binary_op(depth, eb, sb)
        elif choice == 'ternary_op':
            return self.gen_fp_ternary_op(depth, eb, sb)
        elif choice == 'conversion':
            return self.gen_fp_conversion(depth, eb, sb)
        elif choice == 'ite':
            cond = self.gen_bool_term(depth + 1)
            then_term, _, _ = self.gen_fp_term(depth + 1, eb, sb)
            else_term, _, _ = self.gen_fp_term(depth + 1, eb, sb)
            return f"(ite {cond} {then_term} {else_term})", eb, sb
        
        name, _, _ = self.get_or_create_fp_var(eb, sb)
        return name, eb, sb
    
    def gen_fp_unary_op(self, depth, eb, sb):
        op = random.choice(['fp.abs', 'fp.neg', 'fp.sqrt', 'fp.roundToIntegral'])
        fp, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        
        if op in ['fp.sqrt', 'fp.roundToIntegral']:
            rm = self.gen_rounding_mode()
            return f"({op} {rm} {fp})", eb, sb
        else:
            return f"({op} {fp})", eb, sb
    
    def gen_fp_binary_op(self, depth, eb, sb):
        op = random.choice(['fp.add', 'fp.sub', 'fp.mul', 'fp.div', 'fp.rem', 'fp.min', 'fp.max'])
        fp1, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        fp2, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        
        if op in ['fp.add', 'fp.sub', 'fp.mul', 'fp.div']:
            rm = self.gen_rounding_mode()
            return f"({op} {rm} {fp1} {fp2})", eb, sb
        else:
            return f"({op} {fp1} {fp2})", eb, sb
    
    def gen_fp_ternary_op(self, depth, eb, sb):
        rm = self.gen_rounding_mode()
        fp1, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        fp2, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        fp3, _, _ = self.gen_fp_term(depth + 1, eb, sb)
        return f"(fp.fma {rm} {fp1} {fp2} {fp3})", eb, sb
    
    def gen_fp_conversion(self, depth, target_eb, target_sb):
        conv_type = random.choice(['from_bv', 'from_fp', 'from_real', 'from_sbv', 'from_ubv'])
        
        if conv_type == 'from_bv':
            width = target_eb + target_sb
            bv = self.gen_bv_term(width, depth + 1)
            return f"((_ to_fp {target_eb} {target_sb}) {bv})", target_eb, target_sb
        elif conv_type == 'from_fp':
            rm = self.gen_rounding_mode()
            # Pick a different sort to convert from
            source_eb, source_sb = random.choice(self.fp_sorts)
            fp, _, _ = self.gen_fp_term(depth + 1, source_eb, source_sb)
            return f"((_ to_fp {target_eb} {target_sb}) {rm} {fp})", target_eb, target_sb
        elif conv_type == 'from_real':
            rm = self.gen_rounding_mode()
            real = self.gen_real_term(depth + 1)
            return f"((_ to_fp {target_eb} {target_sb}) {rm} {real})", target_eb, target_sb
        elif conv_type == 'from_sbv':
            rm = self.gen_rounding_mode()
            width = random.choice([8, 16, 32, 64])
            bv = self.gen_bv_term(width, depth + 1)
            return f"((_ to_fp {target_eb} {target_sb}) {rm} {bv})", target_eb, target_sb
        else:  # from_ubv
            rm = self.gen_rounding_mode()
            width = random.choice([8, 16, 32, 64])
            bv = self.gen_bv_term(width, depth + 1)
            return f"((_ to_fp_unsigned {target_eb} {target_sb}) {rm} {bv})", target_eb, target_sb
    
    def gen_comparison(self, depth):
        op = random.choice(['fp.leq', 'fp.lt', 'fp.geq', 'fp.gt', 'fp.eq'])
        # Use consistent sort for all arguments
        eb, sb = random.choice(self.fp_sorts)
        num_args = random.randint(2, 4)
        args = []
        for _ in range(num_args):
            arg, _, _ = self.gen_fp_term(depth + 1, eb, sb)
            args.append(arg)
        return f"({op} {' '.join(args)})"
    
    def gen_classification(self, depth):
        op = random.choice([
            'fp.isNormal', 'fp.isSubnormal', 'fp.isZero',
            'fp.isInfinite', 'fp.isNaN', 'fp.isNegative', 'fp.isPositive'
        ])
        fp, _, _ = self.gen_fp_term(depth + 1)
        return f"({op} {fp})"
    
    def gen_bool_term(self, depth=0):
        if depth >= self.max_depth:
            if self.bool_vars and random.random() < 0.5:
                return self.get_or_create_bool_var()
            return random.choice(['true', 'false'])
        
        choices = ['comparison', 'classification', 'literal', 'variable',
                   'and', 'or', 'not', 'implies', 'xor', 'eq', 'distinct', 'ite']
        
        choice = random.choice(choices)
        
        if choice == 'comparison':
            return self.gen_comparison(depth)
        elif choice == 'classification':
            return self.gen_classification(depth)
        elif choice == 'literal':
            return random.choice(['true', 'false'])
        elif choice == 'variable':
            return self.get_or_create_bool_var()
        elif choice == 'and':
            num_args = random.randint(2, 4)
            args = [self.gen_bool_term(depth + 1) for _ in range(num_args)]
            return f"(and {' '.join(args)})"
        elif choice == 'or':
            num_args = random.randint(2, 4)
            args = [self.gen_bool_term(depth + 1) for _ in range(num_args)]
            return f"(or {' '.join(args)})"
        elif choice == 'not':
            arg = self.gen_bool_term(depth + 1)
            return f"(not {arg})"
        elif choice == 'implies':
            num_args = random.randint(2, 3)
            args = [self.gen_bool_term(depth + 1) for _ in range(num_args)]
            return f"(=> {' '.join(args)})"
        elif choice == 'xor':
            arg1 = self.gen_bool_term(depth + 1)
            arg2 = self.gen_bool_term(depth + 1)
            return f"(xor {arg1} {arg2})"
        elif choice == 'eq':
            num_args = random.randint(2, 3)
            args = [self.gen_bool_term(depth + 1) for _ in range(num_args)]
            return f"(= {' '.join(args)})"
        elif choice == 'distinct':
            num_args = random.randint(2, 4)
            args = [self.gen_bool_term(depth + 1) for _ in range(num_args)]
            return f"(distinct {' '.join(args)})"
        elif choice == 'ite':
            cond = self.gen_bool_term(depth + 1)
            then_term = self.gen_bool_term(depth + 1)
            else_term = self.gen_bool_term(depth + 1)
            return f"(ite {cond} {then_term} {else_term})"
        
        return random.choice(['true', 'false'])

def generate_floatingpoint_formula_with_decls():
    gen = FormulaGenerator()
    
    # Initialize with some variables of each sort
    for sort in gen.fp_sorts:
        eb, sb = sort
        num_vars = random.randint(1, 3)
        for _ in range(num_vars):
            gen.add_fp_var(eb, sb)
    
    num_bool_vars = random.randint(1, 3)
    for _ in range(num_bool_vars):
        gen.add_bool_var()
    
    if random.random() < 0.3:
        gen.add_rm_var()
    
    # Generate the formula
    formula = gen.gen_bool_term(depth=0)
    
    decls_str = '\n'.join(gen.decls)
    
    return decls_str, formula