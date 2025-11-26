import random
import string

# Function to generate random symbol names (at least 5 lowercase letters)
def random_symbol(min_len=5):
    length = random.randint(min_len, min_len + 3)
    return ''.join(random.choice(string.ascii_lowercase) for _ in range(length))

# Generate a random integer numeral (e.g., "0", "123")
def random_numeral():
    # avoid leading zeros unless zero itself
    val = random.randint(0, 100)
    return str(val)

# Generate a random decimal literal (e.g., "3.14", "0.5")
def random_decimal():
    integer_part = random.randint(0, 100)
    frac_part = random.randint(1, 999)
    return f"{integer_part}.{frac_part}"

class FuzzContext:
    def __init__(self, max_depth=3):
        self.max_depth = max_depth
        self.int_vars = []  # list of (name, sort)
        self.real_vars = []

    def declare_vars(self, n_int=2, n_real=2):
        # generate fresh variable names and collect declarations
        for _ in range(n_int):
            sym = random_symbol()
            self.int_vars.append((sym, 'Int'))
        for _ in range(n_real):
            sym = random_symbol()
            self.real_vars.append((sym, 'Real'))

    def decls_smt2(self):
        lines = []
        for name, sort in self.int_vars + self.real_vars:
            lines.append(f"(declare-fun {name} () {sort})")
        return "\n".join(lines)

    def pick_int_var(self):
        return random.choice(self.int_vars)[0] if self.int_vars else None

    def pick_real_var(self):
        return random.choice(self.real_vars)[0] if self.real_vars else None

    def gen_int_expr(self, depth):
        if depth <= 0 or random.random() < 0.3:
            # base: numeral or variable
            if random.random() < 0.5 and self.int_vars:
                return self.pick_int_var()
            else:
                return random_numeral()
        # choose an IntExpr form
        choice = random.choice(['neg_num', 'neg_expr', 'plus', 'mul', 'div', 'mod', 'abs', 'to_int'])
        if choice == 'neg_num':
            return f"(- {random_numeral()})"
        if choice == 'neg_expr':
            e = self.gen_int_expr(depth - 1)
            f = self.gen_int_expr(depth - 1)
            return f"(- {e} {f})"
        if choice == 'plus':
            elems = [self.gen_int_expr(depth - 1) for _ in range(random.randint(2, 4))]
            return f"(+ {' '.join(elems)})"
        if choice == 'mul':
            elems = [self.gen_int_expr(depth - 1) for _ in range(random.randint(2, 4))]
            return f"(* {' '.join(elems)})"
        if choice == 'div':
            elems = [self.gen_int_expr(depth - 1) for _ in range(2)]
            return f"(div {' '.join(elems)})"
        if choice == 'mod':
            a = self.gen_int_expr(depth - 1)
            b = self.gen_int_expr(depth - 1)
            return f"(mod {a} {b})"
        if choice == 'abs':
            e = self.gen_int_expr(depth - 1)
            return f"(abs {e})"
        if choice == 'to_int':
            r = self.gen_real_expr(depth - 1)
            return f"(to_int {r})"
        # fallback
        return random_numeral()

    def gen_real_expr(self, depth):
        if depth <= 0 or random.random() < 0.3:
            # base: decimal or to_real variable
            if random.random() < 0.5 and self.real_vars:
                return self.pick_real_var()
            if random.random() < 0.5 and self.int_vars:
                v = self.pick_int_var()
                return f"(to_real {v})"
            return random_decimal()
        choice = random.choice(['neg', 'sub', 'plus', 'mul', 'div', 'to_real'])
        if choice == 'neg':
            e = self.gen_real_expr(depth - 1)
            return f"(- {e})"
        if choice == 'sub':
            e1 = self.gen_real_expr(depth - 1)
            e2 = self.gen_real_expr(depth - 1)
            return f"(- {e1} {e2})"
        if choice == 'plus':
            elems = [self.gen_real_expr(depth - 1) for _ in range(random.randint(2, 4))]
            return f"(+ {' '.join(elems)})"
        if choice == 'mul':
            elems = [self.gen_real_expr(depth - 1) for _ in range(random.randint(2, 4))]
            return f"(* {' '.join(elems)})"
        if choice == 'div':
            elems = [self.gen_real_expr(depth - 1) for _ in range(2)]
            return f"(/ {' '.join(elems)})"
        if choice == 'to_real':
            i = self.gen_int_expr(depth - 1)
            return f"(to_real {i})"
        return random_decimal()

    def gen_sorted_expr(self, depth):
        # choose Int or Real
        if random.random() < 0.5:
            return self.gen_int_expr(depth)
        else:
            return self.gen_real_expr(depth)

    def gen_bool_expr(self, depth):
        if depth <= 0:
            # base Boolean: comparison of two sorted exprs
            op = random.choice(['<', '<=', '>', '>=', '=', 'distinct'])
            a = self.gen_sorted_expr(1)
            b = self.gen_sorted_expr(1)
            # possibly chain
            if op in ['<', '<=', '>', '>='] and random.random() < 0.5:
                c = self.gen_sorted_expr(1)
                return f"({op} {a} {b} {c})"
            return f"({op} {a} {b})"
        choice = random.choice(['comp', '=', 'distinct', 'is_int', 'divisible', 
                                'not', 'and', 'or', 'imp', 'quant'])
        if choice in ['comp', '=', 'distinct']:
            op = choice if choice != 'comp' else random.choice(['<', '<=', '>', '>='])
            a = self.gen_sorted_expr(depth-1)
            b = self.gen_sorted_expr(depth-1)
            return f"({op} {a} {b})"
        if choice == 'is_int':
            r = self.gen_real_expr(depth-1)
            return f"(is_int {r})"
        if choice == 'divisible':
            n = random_numeral()
            e = self.gen_int_expr(depth-1)
            return f"((_ divisible {n}) {e})"
        if choice == 'not':
            e = self.gen_bool_expr(depth-1)
            return f"(not {e})"
        if choice == 'and':
            parts = [self.gen_bool_expr(depth-1) for _ in range(random.randint(2,3))]
            return f"(and {' '.join(parts)})"
        if choice == 'or':
            parts = [self.gen_bool_expr(depth-1) for _ in range(random.randint(2,3))]
            return f"(or {' '.join(parts)})"
        if choice == 'imp':
            a = self.gen_bool_expr(depth-1)
            b = self.gen_bool_expr(depth-1)
            return f"(=> {a} {b})"
        if choice == 'quant':
            q = random.choice(['forall', 'exists'])
            # pick 1-2 vars to bind
            vars_to_bind = []
            for _ in range(random.randint(1,2)):
                if random.random() < 0.5 and self.int_vars:
                    vars_to_bind.append((self.pick_int_var(), 'Int'))
                elif self.real_vars:
                    vars_to_bind.append((self.pick_real_var(), 'Real'))
            decls = ' '.join(f"({v} {s})" for v,s in vars_to_bind)
            body = self.gen_bool_expr(depth-1)
            return f"({q} ({decls}) {body})"
        # fallback comparison
        return self.gen_bool_expr(0)


def generate_reals_ints_formula_with_decls():
    """
    Generate random SMT-LIB2 declarations and a Boolean formula in the Reals_Ints theory.

    Returns:
      decls : str   -- SMT-LIB2 declarations (declare-fun ...) for all variables.
      formula : str -- A single Boolean term (without assert) conforming to the Reals_Ints grammar.
    """
    ctx = FuzzContext(max_depth=4)
    # declare a few variables for each sort
    ctx.declare_vars(n_int=random.randint(1,3), n_real=random.randint(1,3))
    decls = ctx.decls_smt2()
    formula = ctx.gen_bool_expr(ctx.max_depth)
    return decls, formula

# Example usage:
if __name__ == "__main__":
    d, f = generate_reals_ints_formula_with_decls()
    print("; Declarations:")
    print(d)
    print("; Formula:")
    print(f)
