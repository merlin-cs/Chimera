import random
import string

def generate_symbol():
    """Generate a random lowercase ASCII symbol of length ≥5."""
    return ''.join(random.choices(string.ascii_lowercase, k=5))

def generate_string_literal():
    """Generate a random printable ASCII string literal with SMT-LIB escaping."""
    length = random.randint(1, 3)
    content = ''.join(random.choices(string.ascii_letters + string.digits + ' ', k=length))
    return f'"{content}"'

def generate_hex():
    """Generate a random #x hexadecimal code with 1–5 digits."""
    length = random.randint(1, 5)
    digits = random.choices(string.hexdigits.upper(), k=length)
    return '#x' + ''.join(digits)

def generate_unicode_hex():
    """Generate a random #x hexadecimal code for valid Unicode characters (< 0x30000)."""
    # Generate a random value between 0 and 0x2FFFF (196607)
    max_code_point = 0x2FFFF
    code_point = random.randint(0, max_code_point)
    return f'#x{code_point:X}'

class FormulaGenerator:
    def __init__(self, max_depth=3):
        self.max_depth = max_depth
        self.str_vars = set()
        self.int_vars = set()
        self.re_vars = set()

    def new_var(self, sort):
        name = generate_symbol()
        if sort == 'String':
            self.str_vars.add(name)
        elif sort == 'Int':
            self.int_vars.add(name)
        else:
            self.re_vars.add(name)
        return name

    def gen_string_term(self, depth):
        if depth <= 0:
            if random.random() < 0.5:
                var = self.new_var('String')
                return var
            else:
                return generate_string_literal()
        choice = random.choice([
            'symbol', 'literal', 'char', 'concat', 'at', 'substr',
            'from_code'
        ])
        if choice == 'symbol':
            return self.new_var('String')
        if choice == 'literal':
            return generate_string_literal()
        if choice == 'char':
            return f'(_ char {generate_unicode_hex()})'
        if choice == 'concat':
            return f'(str.++ {self.gen_string_term(depth-1)} {self.gen_string_term(depth-1)})'
        if choice == 'at':
            return f'(str.at {self.gen_string_term(depth-1)} {self.gen_int_term(depth-1)})'
        if choice == 'substr':
            return f'(str.substr {self.gen_string_term(depth-1)} {self.gen_int_term(depth-1)} {self.gen_int_term(depth-1)})'
        # fallback
        return generate_string_literal()

    def gen_int_term(self, depth):
        if depth <= 0:
            if random.random() < 0.5:
                var = self.new_var('Int')
                return var
            else:
                return str(random.randint(0, 10))
        choice = random.choice(['symbol', 'numeral', 'len', 'indexof'])
        if choice == 'symbol':
            return self.new_var('Int')
        if choice == 'numeral':
            return str(random.randint(0, 10))
        if choice == 'len':
            return f'(str.len {self.gen_string_term(depth-1)})'
        if choice == 'indexof':
            return f'(str.indexof {self.gen_string_term(depth-1)} {self.gen_string_term(depth-1)} {self.gen_int_term(depth-1)})'
        # fallback
        return str(random.randint(0, 10))

    def gen_regex_term(self, depth):
        if depth <= 0:
            if random.random() < 0.5:
                return self.new_var('RegLan')
            else:
                return '(re.none)'
        choice = random.choice(['symbol', 'none', 'allchar', 'to_re', 'union'])
        if choice == 'symbol':
            return self.new_var('RegLan')
        if choice == 'none':
            return '(re.none)'
        if choice == 'allchar':
            return '(re.allchar)'
        if choice == 'to_re':
            return f'(str.to_re {self.gen_string_term(depth-1)})'
        if choice == 'union':
            return f'(re.union {self.gen_regex_term(depth-1)} {self.gen_regex_term(depth-1)})'
        # fallback
        return '(re.none)'

    def gen_bool_expr(self, depth):
        if depth <= 0:
            return self.gen_atom()
        choice = random.choice(['atom', 'not', 'and', 'or', 'imp', 'ite'])
        if choice == 'atom':
            return self.gen_atom()
        if choice == 'not':
            return f'(not {self.gen_bool_expr(depth-1)})'
        if choice == 'and':
            return f'(and {" ".join(self.gen_bool_expr(depth-1) for _ in range(random.randint(2, 3)))})'
        if choice == 'or':
            return f'(or {" ".join(self.gen_bool_expr(depth-1) for _ in range(random.randint(2, 3)))})'
        if choice == 'imp':
            return f'(=> {self.gen_bool_expr(depth-1)} {self.gen_bool_expr(depth-1)})'
        if choice == 'ite':
            return f'(ite {self.gen_bool_expr(depth-1)} {self.gen_bool_expr(depth-1)} {self.gen_bool_expr(depth-1)})'
        # fallback
        return self.gen_atom()

    def gen_atom(self):
        choice = random.choice(['eq', 'distinct', 'lt', 'contains'])
        if choice == 'eq':
            return f'(= {self.gen_string_term(1)} {self.gen_string_term(1)})'
        if choice == 'distinct':
            t1 = self.gen_string_term(1)
            t2 = self.gen_string_term(1)
            return f'(distinct {t1} {t2})'
        if choice == 'lt':
            return f'(str.< {self.gen_string_term(1)} {self.gen_string_term(1)})'
        if choice == 'contains':
            return f'(str.contains {self.gen_string_term(1)} {self.gen_string_term(1)})'

def generate_strings_formula_with_decls():
    """
    Generates SMT-LIB2 declarations and a single Boolean formula term
    in the Strings theory.
    Returns:
        decls (str): SMT-LIB2 declarations for all used vars.
        formula (str): A well-formed Boolean term.
    """
    gen = FormulaGenerator()
    formula = gen.gen_bool_expr(gen.max_depth)
    decls = []
    for v in sorted(gen.str_vars):
        decls.append(f'(declare-const {v} String)')
    for v in sorted(gen.int_vars):
        decls.append(f'(declare-const {v} Int)')
    for v in sorted(gen.re_vars):
        decls.append(f'(declare-const {v} RegLan)')
    return '\n'.join(decls), formula

# Example usage
if __name__ == "__main__":
    decls_str, formula_str = generate_strings_formula_with_decls()
    print(";; Declarations:")
    print(decls_str)
    print("\n;; Formula:")
    print(formula_str)