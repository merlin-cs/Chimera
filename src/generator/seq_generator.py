import random

class SeqFormulaGenerator:
    def __init__(self,
                 num_bool_vars=3,
                 num_int_vars=3,
                 num_seq_vars=3,
                 num_elem_vars=3,
                 elem_sort='Int',
                 seq_sort='(Seq Int)',
                 max_depth=3,
                 seed=None):
        """
        Initialize the random formula generator.

        :param num_bool_vars: Number of Boolean variables (e.g., p, q)
        :param num_int_vars: Number of Integer variables (e.g., i, j)
        :param num_seq_vars: Number of Sequence variables (e.g., x, y)
        :param num_elem_vars: Number of Element variables (elements of sequences)
        :param elem_sort: Sort of elements (e.g., 'Int' or 'String')
        :param seq_sort: SMT-LIB sequence sort (e.g., '(Seq Int)')
        :param max_depth: Maximum recursion depth for term generation
        :param seed: Optional random seed for reproducibility
        """
        if seed is not None:
            random.seed(seed)
        self.max_depth = max_depth
        self.elem_sort = elem_sort
        self.seq_sort = seq_sort

        # Generate variable names
        self.bool_vars = [f'p{i}_{random.randint(1,1000)}' for i in range(num_bool_vars)]
        self.int_vars = [f'i{i}_{random.randint(1,1000)}' for i in range(num_int_vars)]
        self.seq_vars = [f's{i}_{random.randint(1,1000)}' for i in range(num_seq_vars)]
        self.elem_vars = [f'e{i}_{random.randint(1,1000)}' for i in range(num_elem_vars)]

    def decls(self):
        """Produce SMT-LIB declarations for all variables."""
        lines = []
        for v in self.bool_vars:
            lines.append(f'(declare-fun {v} () Bool)')
        for v in self.int_vars:
            lines.append(f'(declare-fun {v} () Int)')
        for v in self.seq_vars:
            lines.append(f'(declare-fun {v} () {self.seq_sort})')
        for v in self.elem_vars:
            lines.append(f'(declare-fun {v} () {self.elem_sort})')
        return "\n".join(lines)

    def gen_bool(self, depth=None):
        """Generate a random BoolTerm."""
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            # Base cases
            choice = random.choice(['true', 'false', 'var'])
            if choice == 'var' and self.bool_vars:
                return random.choice(self.bool_vars)
            return random.choice(['true', 'false'])

        ops = ['and', 'or', 'not', '=>', 'xor', 'ite',
               '=', 'distinct', '<', '<=', '>', '>=',
               'seq.contains', 'seq.prefixof', 'seq.suffixof']
        op = random.choice(ops)
        if op in ['true', 'false']:
            return op
        if op == 'var':
            return random.choice(self.bool_vars)
        # handle different arities
        if op in ['and', 'or', 'xor', '=>']:
            # n-ary, at least 2
            n = random.randint(2, 3)
            terms = [self.gen_bool(depth-1) for _ in range(n)]
            return f'({op} ' + ' '.join(terms) + ')'
        if op == 'not':
            t = self.gen_bool(depth-1)
            return f'(not {t})'
        if op == 'ite':
            c = self.gen_bool(depth-1)
            t1 = self.gen_bool(depth-1)
            t2 = self.gen_bool(depth-1)
            return f'(ite {c} {t1} {t2})'
        if op in ['=', 'distinct']:
            # Choose a specific type for both operands to ensure type consistency
            term_type = random.choice(['bool', 'seq', 'int', 'elem'])
            if term_type == 'bool':
                t1 = self.gen_bool(depth-1)
                t2 = self.gen_bool(depth-1)
            elif term_type == 'seq':
                t1 = self.gen_seq(depth-1)
                t2 = self.gen_seq(depth-1)
            elif term_type == 'int':
                t1 = self.gen_int(depth-1)
                t2 = self.gen_int(depth-1)
            else:  # elem
                t1 = self.gen_elem(depth-1)
                t2 = self.gen_elem(depth-1)
            
            rest = ''
            if op == 'distinct' and random.choice([True, False]):
                # 3-ary distinct - generate third term of same type
                if term_type == 'bool':
                    t3 = self.gen_bool(depth-1)
                elif term_type == 'seq':
                    t3 = self.gen_seq(depth-1)
                elif term_type == 'int':
                    t3 = self.gen_int(depth-1)
                else:  # elem
                    t3 = self.gen_elem(depth-1)
                rest = ' ' + t3
            return f'({op} {t1} {t2}{rest})'
        if op in ['<', '<=', '>', '>=']:
            t1 = self.gen_int(depth-1)
            t2 = self.gen_int(depth-1)
            return f'({op} {t1} {t2})'
        # sequence predicates
        if op.startswith('seq.'):
            t1 = self.gen_seq(depth-1)
            t2 = self.gen_seq(depth-1)
            return f'({op} {t1} {t2})'
        # fallback
        return 'true'

    def gen_seq(self, depth=None):
        """Generate a random SeqTerm."""
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            # base: variable or literal empty
            if self.seq_vars and random.choice([True, False]):
                return random.choice(self.seq_vars)
            return f'(as seq.empty {self.seq_sort})'

        ops = ['seq.unit', 'seq.++', 'seq.update', 'seq.extract',
               'seq.at', 'seq.replace', 'seq.replace_all', 'seq.rev', 'ite']
        op = random.choice(ops)
        if op == 'seq.unit':
            e = self.gen_elem(depth-1)
            return f'(seq.unit {e})'
        if op == 'seq.++':
            s1 = self.gen_seq(depth-1)
            s2 = self.gen_seq(depth-1)
            return f'(seq.++ {s1} {s2})'
        if op == 'seq.update':
            s = self.gen_seq(depth-1)
            i = self.gen_int(depth-1)
            e = self.gen_seq(depth-1)
            return f'(seq.update {s} {i} {e})'
        if op == 'seq.extract':
            s = self.gen_seq(depth-1)
            i = self.gen_int(depth-1)
            j = self.gen_int(depth-1)
            return f'(seq.extract {s} {i} {j})'
        if op == 'seq.at':
            s = self.gen_seq(depth-1)
            i = self.gen_int(depth-1)
            return f'(seq.at {s} {i})'
        if op in ['seq.replace', 'seq.replace_all']:
            s = self.gen_seq(depth-1)
            t = self.gen_seq(depth-1)
            u = self.gen_seq(depth-1)
            return f'({op} {s} {t} {u})'
        if op == 'seq.rev':
            s = self.gen_seq(depth-1)
            return f'(seq.rev {s})'
        if op == 'ite':
            c = self.gen_bool(depth-1)
            t1 = self.gen_seq(depth-1)
            t2 = self.gen_seq(depth-1)
            return f'(ite {c} {t1} {t2})'
        # fallback
        return random.choice(self.seq_vars or [f'(as seq.empty {self.seq_sort})'])

    def gen_int(self, depth=None):
        """Generate a random IntTerm."""
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            if self.int_vars and random.choice([True, False]):
                return random.choice(self.int_vars)
            return str(random.randint(0, 10))

        ops = ['seq.len', 'seq.indexof', '+', '-', '*', 'div', 'mod', 'abs', 'ite']
        op = random.choice(ops)
        if op == 'seq.len':
            s = self.gen_seq(depth-1)
            return f'(seq.len {s})'
        if op == 'seq.indexof':
            s = self.gen_seq(depth-1)
            t = self.gen_seq(depth-1)
            i = self.gen_int(depth-1)
            return f'(seq.indexof {s} {t} {i})'
        if op in ['+', '*', 'div']:
            n = random.randint(2, 3)
            terms = [self.gen_int(depth-1) for _ in range(n)]
            return f'({op} ' + ' '.join(terms) + ')'
        if op == '-':
            # unary or binary
            if random.choice([True, False]):
                t = self.gen_int(depth-1)
                return f'(- {t})'
            i1 = self.gen_int(depth-1)
            i2 = self.gen_int(depth-1)
            return f'(- {i1} {i2})'
        if op == 'mod':
            i1 = self.gen_int(depth-1)
            i2 = self.gen_int(depth-1)
            return f'(mod {i1} {i2})'
        if op == 'abs':
            t = self.gen_int(depth-1)
            return f'(abs {t})'
        if op == 'ite':
            c = self.gen_bool(depth-1)
            t1 = self.gen_int(depth-1)
            t2 = self.gen_int(depth-1)
            return f'(ite {c} {t1} {t2})'
        # fallback
        return str(random.randint(0, 10))

    def gen_elem(self, depth=None):
        """Generate a random ElementTerm."""
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            # base: variable or literal
            if self.elem_vars and random.choice([True, False]):
                return random.choice(self.elem_vars)
            # literal
            if self.elem_sort == 'Int':
                return str(random.randint(0, 10))
            if self.elem_sort == 'String':
                c = random.choice('abcdefghijklmnopqrstuvwxyz')
                return f'"{c}"'
            return random.choice(self.elem_vars or ['0'])

        # use seq.nth or ite
        if random.choice([True, False]):
            s = self.gen_seq(depth-1)
            i = self.gen_int(depth-1)
            return f'(seq.nth {s} {i})'
        # ite
        c = self.gen_bool(depth-1)
        e1 = self.gen_elem(depth-1)
        e2 = self.gen_elem(depth-1)
        return f'(ite {c} {e1} {e2})'

    def gen_term(self, depth=None):
        """Generate a generic term (could be bool, seq, int, or elem) for equality/distinct."""
        # randomly pick type
        t = random.choice(['bool', 'seq', 'int', 'elem'])
        if t == 'bool':
            return self.gen_bool(depth)
        if t == 'seq':
            return self.gen_seq(depth)
        if t == 'int':
            return self.gen_int(depth)
        return self.gen_elem(depth)

    def generate(self):
        """Produce a full SMT-LIB snippet with declarations and a random Boolean formula asserted."""
        decls = self.decls()
        formula = self.gen_bool()
        # return decls + "\n(assert " + formula + ")\n(check-sat)" 
        return decls, formula


def generate_seq_formula_with_decls():
    """
    Generate SMT-LIB script with sequence declarations and a random formula.
    """
    gen = SeqFormulaGenerator()
    return gen.generate()

# Example usage:
if __name__ == '__main__':
    gen = SeqFormulaGenerator(seed=42)
    print(gen.generate())
