# complete Python module
import random
import string

# A set of SMT-LIB keywords to avoid for generated symbol names.
_SMT_KEYWORDS = {
    "and", "or", "not", "xor", "=>", "ite", "true", "false", "assert",
    "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
    "declare-sort", "define-fun", "define-fun-rec", "define-sort",
    "echo", "exit", "get-assertions", "get-assignment", "get-info",
    "get-model", "get-option", "get-proof", "get-unsat-assumptions",

    "get-unsat-core", "get-value", "pop", "push", "reset", "reset-assertions",
    "set-info", "set-logic", "set-option", "par", "NUMERAL", "DECIMAL",
    "STRING", "continued-execution", "error", "immediate-exit", "incomplete",
    "logic", "memout", "sat", "success", "theory", "unknown", "unsupported",
    "unsat", "seq.++", "seq.at", "seq.contains", "seq.extract", "seq.indexof",
    "seq.len", "seq.nth", "seq.prefixof", "seq.replace", "seq.replace_all",
    "seq.rev", "seq.suffixof", "seq.unit", "seq.update", "str.++", "str.at",
    "str.contains", "str.indexof", "str.is_digit", "str.len", "str.prefixof",
    "str.replace", "str.replace_all", "str.suffixof", "str.to_int",
    "str.substr", "int.to_str", "as", "let", "forall", "exists", "match",
    "_", "!", "BitVec", "Int", "Bool", "String", "Seq", "Array", "RoundingMode",
    "Real", "Float16", "Float32", "Float64", "Float128", "fp", "to_fp",
    "to_fp_unsigned", "fp.abs", "fp.add", "fp.div", "fp.eq", "fp.isInfinite",
    "fp.isNaN", "fp.isNegative", "fp.isNormal", "fp.isPositive", "fp.isZero",
    "fp.lt", "fp.mul", "fp.neg", "fp.rem", "fp.roundToIntegral", "fp.sqrt",
    "fp.sub", "RNE", "RNA", "RTP", "RTN", "RTZ",
}

_MIN_SYMBOL_LEN = 5
_MAX_SYMBOL_LEN = 10
_MAX_NARY_ARGS = 4
_MAX_DEPTH = 5
_MAX_VARS_PER_SORT = 4


class _FormulaGenerator:
    """Encapsulates the state and logic for generating a random formula."""

    def __init__(self):
        self.used_names = set(_SMT_KEYWORDS)
        self.decls = []
        self.vars = {'Bool': [], 'Int': [], 'Seq': [], 'Elem': []}
        self.max_depth = random.randint(3, _MAX_DEPTH + 1)

        self.elem_sort_name = ""
        self.elem_sort_def = ""
        self.elem_bv_width = 0
        self.seq_sort_def = ""

    def _generate_symbol(self) -> str:
        """Generates a new, unique symbol name."""
        while True:
            length = random.randint(_MIN_SYMBOL_LEN, _MAX_SYMBOL_LEN)
            name = ''.join(random.choices(string.ascii_lowercase, k=length))
            if name not in self.used_names:
                self.used_names.add(name)
                return name

    def _initialize_sorts(self):
        """Randomly chooses and declares the element sort for sequences."""
        sort_choice = random.choice(['Int', 'String', 'BitVec', 'Custom'])
        if sort_choice == 'Int':
            self.elem_sort_name = 'Int'
            self.elem_sort_def = 'Int'
        elif sort_choice == 'String':
            self.elem_sort_name = 'String'
            self.elem_sort_def = 'String'
        elif sort_choice == 'BitVec':
            self.elem_bv_width = random.choice([8, 16, 32])
            self.elem_sort_name = f'(_ BitVec {self.elem_bv_width})'
            self.elem_sort_def = f'(_ BitVec {self.elem_bv_width})'
        else:  # Custom sort
            self.elem_sort_name = self._generate_symbol()
            self.elem_sort_def = self.elem_sort_name
            self.decls.append(f"(declare-sort {self.elem_sort_name} 0)")

        self.seq_sort_def = f"(Seq {self.elem_sort_def})"

    def _initialize_vars(self):
        """Declares a random number of variables for each sort."""
        sort_map = {
            'Bool': 'Bool',
            'Int': 'Int',
            'Seq': self.seq_sort_def,
            'Elem': self.elem_sort_def
        }
        for sort_key, sort_smt_name in sort_map.items():
            num_vars = random.randint(1, _MAX_VARS_PER_SORT)
            for _ in range(num_vars):
                var_name = self._generate_symbol()
                self.vars[sort_key].append(var_name)
                self.decls.append(f"(declare-const {var_name} {sort_smt_name})")

    def _choose_producer(self, producers, terminal_producers, depth):
        """Selects a production rule based on depth."""
        if depth >= self.max_depth:
            prods, weights = zip(*terminal_producers.items())
        else:
            # At deeper levels, prefer terminals to ensure termination
            depth_factor = depth / self.max_depth
            
            # Combine producers, giving terminals higher weight as depth increases
            all_producers = list(producers.items())
            term_producers = list(terminal_producers.items())

            prods = [p for p, w in all_producers]
            weights = [w * (1 - depth_factor) for p, w in all_producers]

            term_prods_map = dict(term_producers)
            for i, p in enumerate(prods):
                if p in term_prods_map:
                    weights[i] += term_prods_map[p] * depth_factor * 2

        return random.choices(prods, weights=weights, k=1)[0]

    # --- Literal Generators ---

    def _generate_bool_literal(self) -> str:
        return random.choice(["true", "false"])

    def _generate_numeral(self) -> str:
        return str(random.randint(-100, 100))

    def _generate_string_literal(self) -> str:
        length = random.randint(0, 10)
        chars = [c for c in string.ascii_letters + string.digits if c != '"']
        if not chars: return '""'
        return '"' + ''.join(random.choices(chars, k=length)) + '"'

    def _generate_bitvec_literal(self) -> str:
        val = random.randint(0, (1 << self.elem_bv_width) - 1)
        return f"(_ bv{val} {self.elem_bv_width})"

    def _generate_elem_literal(self) -> str:
        if self.elem_sort_def == 'Int':
            return self._generate_numeral()
        if self.elem_sort_def == 'String':
            return self._generate_string_literal()
        if self.elem_sort_def.startswith('(_ BitVec'):
            return self._generate_bitvec_literal()
        # For custom sorts, we cannot generate literals, so we must use a variable.
        # This case is handled by the term generators.
        return ""

    # --- Term Generators ---

    def _generate_term_of_sort(self, sort_key: str, depth: int) -> str:
        """Dispatcher to generate a term of a specific sort."""
        if sort_key == 'Bool':
            return self._generate_bool_term(depth)
        if sort_key == 'Int':
            return self._generate_int_term(depth)
        if sort_key == 'Seq':
            return self._generate_seq_term(depth)
        if sort_key == 'Elem':
            return self._generate_elem_term(depth)
        raise ValueError(f"Unknown sort key: {sort_key}")

    def _generate_bool_term(self, depth: int) -> str:
        producers = {
            self._prod_bool_var: 10,
            self._prod_bool_literal: 2,
            self._prod_equals: 10,
            self._prod_distinct: 5,
            self._prod_not: 8,
            self._prod_nary_bool("and"): 10,
            self._prod_nary_bool("or"): 10,
            self._prod_nary_bool("xor"): 5,
            self._prod_nary_bool("=>"): 5,
            self._prod_ite_bool: 8,
            self._prod_int_compare: 10,
            self._prod_seq_pred("seq.contains"): 8,
            self._prod_seq_pred("seq.prefixof"): 8,
            self._prod_seq_pred("seq.suffixof"): 8,
        }
        terminal_producers = {
            self._prod_bool_var: 10,
            self._prod_bool_literal: 5,
        }
        chosen_producer = self._choose_producer(producers, terminal_producers, depth)
        return chosen_producer(depth)

    def _generate_seq_term(self, depth: int) -> str:
        producers = {
            self._prod_seq_var: 10,
            self._prod_seq_empty: 2,
            self._prod_seq_unit: 8,
            self._prod_seq_concat: 10,
            self._prod_seq_update: 5,
            self._prod_seq_extract: 8,
            self._prod_seq_at: 3, # at is a partial function, less frequent
            self._prod_seq_replace: 8,
            self._prod_seq_replace_all: 8,
            self._prod_seq_rev: 5,
            self._prod_ite_seq: 8,
        }
        terminal_producers = {
            self._prod_seq_var: 10,
            self._prod_seq_empty: 5,
        }
        chosen_producer = self._choose_producer(producers, terminal_producers, depth)
        return chosen_producer(depth)

    def _generate_int_term(self, depth: int) -> str:
        producers = {
            self._prod_int_var: 10,
            self._prod_numeral: 5,
            self._prod_seq_len: 10,
            self._prod_seq_indexof: 8,
            self._prod_nary_int("+"): 10,
            self._prod_nary_int("*"): 8,
            self._prod_unary_binary_int("-"): 8,
            self._prod_ite_int: 8,
        }
        terminal_producers = {
            self._prod_int_var: 10,
            self._prod_numeral: 5,
        }
        chosen_producer = self._choose_producer(producers, terminal_producers, depth)
        return chosen_producer(depth)

    def _generate_elem_term(self, depth: int) -> str:
        producers = {
            self._prod_elem_var: 10,
            self._prod_seq_nth: 8,
            self._prod_ite_elem: 8,
        }
        # Literals are only possible for certain sorts
        if self.elem_sort_def in ['Int', 'String'] or self.elem_sort_def.startswith('(_ BitVec'):
            producers[self._prod_elem_literal] = 5

        terminal_producers = {self._prod_elem_var: 10}
        if self.elem_sort_def in ['Int', 'String'] or self.elem_sort_def.startswith('(_ BitVec'):
            terminal_producers[self._prod_elem_literal] = 5

        chosen_producer = self._choose_producer(producers, terminal_producers, depth)
        return chosen_producer(depth)

    # --- Production Rule Implementations ---

    # Bool productions
    def _prod_bool_var(self, depth: int) -> str:
        return random.choice(self.vars['Bool'])
    def _prod_bool_literal(self, depth: int) -> str:
        return self._generate_bool_literal()
    def _prod_equals(self, depth: int) -> str:
        sort_key = random.choice(['Bool', 'Int', 'Seq', 'Elem'])
        # Avoid equality on custom sorts if no variables exist
        if sort_key == 'Elem' and not self.vars['Elem'] and self._generate_elem_literal() == "":
            sort_key = 'Int'
        t1 = self._generate_term_of_sort(sort_key, depth + 1)
        t2 = self._generate_term_of_sort(sort_key, depth + 1)
        return f"(= {t1} {t2})"
    def _prod_distinct(self, depth: int) -> str:
        sort_key = random.choice(['Int', 'Seq', 'Elem'])
        if sort_key == 'Elem' and not self.vars['Elem'] and self._generate_elem_literal() == "":
            sort_key = 'Int'
        n = random.randint(2, _MAX_NARY_ARGS)
        terms = [self._generate_term_of_sort(sort_key, depth + 1) for _ in range(n)]
        return f"(distinct {' '.join(terms)})"
    def _prod_not(self, depth: int) -> str:
        return f"(not {self._generate_bool_term(depth + 1)})"
    def _prod_nary_bool(self, op: str):
        def _prod(depth: int) -> str:
            n = random.randint(2, _MAX_NARY_ARGS)
            args = [self._generate_bool_term(depth + 1) for _ in range(n)]
            return f"({op} {' '.join(args)})"
        return _prod
    def _prod_ite_bool(self, depth: int) -> str:
        c = self._generate_bool_term(depth + 1)
        t = self._generate_bool_term(depth + 1)
        e = self._generate_bool_term(depth + 1)
        return f"(ite {c} {t} {e})"
    def _prod_int_compare(self, depth: int) -> str:
        op = random.choice(["<", "<=", ">", ">="])
        t1 = self._generate_int_term(depth + 1)
        t2 = self._generate_int_term(depth + 1)
        return f"({op} {t1} {t2})"
    def _prod_seq_pred(self, op: str):
        def _prod(depth: int) -> str:
            s1 = self._generate_seq_term(depth + 1)
            s2 = self._generate_seq_term(depth + 1)
            return f"({op} {s1} {s2})"
        return _prod

    # Seq productions
    def _prod_seq_var(self, depth: int) -> str:
        return random.choice(self.vars['Seq'])
    def _prod_seq_empty(self, depth: int) -> str:
        return f'(as seq.empty (Seq {self.elem_sort_def}))'
    def _prod_seq_unit(self, depth: int) -> str:
        e = self._generate_elem_term(depth + 1)
        return f"(seq.unit {e})"
    def _prod_seq_concat(self, depth: int) -> str:
        n = random.randint(2, _MAX_NARY_ARGS)
        args = [self._generate_seq_term(depth + 1) for _ in range(n)]
        return f"(seq.++ {' '.join(args)})"
    def _prod_seq_update(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        i = self._generate_int_term(depth + 1)
        sub = self._generate_seq_term(depth + 1) # Note: spec says (Seq S)
        return f"(seq.update {s} {i} {sub})"
    def _prod_seq_extract(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        i = self._generate_int_term(depth + 1)
        ln = self._generate_int_term(depth + 1)
        return f"(seq.extract {s} {i} {ln})"
    def _prod_seq_at(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        i = self._generate_int_term(depth + 1)
        return f"(seq.at {s} {i})"
    def _prod_seq_replace(self, depth: int) -> str:
        s1 = self._generate_seq_term(depth + 1)
        s2 = self._generate_seq_term(depth + 1)
        s3 = self._generate_seq_term(depth + 1)
        return f"(seq.replace {s1} {s2} {s3})"
    def _prod_seq_replace_all(self, depth: int) -> str:
        s1 = self._generate_seq_term(depth + 1)
        s2 = self._generate_seq_term(depth + 1)
        s3 = self._generate_seq_term(depth + 1)
        return f"(seq.replace_all {s1} {s2} {s3})"
    def _prod_seq_rev(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        return f"(seq.rev {s})"
    def _prod_ite_seq(self, depth: int) -> str:
        c = self._generate_bool_term(depth + 1)
        t = self._generate_seq_term(depth + 1)
        e = self._generate_seq_term(depth + 1)
        return f"(ite {c} {t} {e})"

    # Int productions
    def _prod_int_var(self, depth: int) -> str:
        return random.choice(self.vars['Int'])
    def _prod_numeral(self, depth: int) -> str:
        return self._generate_numeral()
    def _prod_seq_len(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        return f"(seq.len {s})"
    def _prod_seq_indexof(self, depth: int) -> str:
        s1 = self._generate_seq_term(depth + 1)
        s2 = self._generate_seq_term(depth + 1)
        i = self._generate_int_term(depth + 1)
        return f"(seq.indexof {s1} {s2} {i})"
    def _prod_nary_int(self, op: str):
        def _prod(depth: int) -> str:
            n = random.randint(2, _MAX_NARY_ARGS)
            args = [self._generate_int_term(depth + 1) for _ in range(n)]
            return f"({op} {' '.join(args)})"
        return _prod
    def _prod_unary_binary_int(self, op: str):
        def _prod(depth: int) -> str:
            n = random.randint(1, 2)
            args = [self._generate_int_term(depth + 1) for _ in range(n)]
            return f"({op} {' '.join(args)})"
        return _prod
    def _prod_ite_int(self, depth: int) -> str:
        c = self._generate_bool_term(depth + 1)
        t = self._generate_int_term(depth + 1)
        e = self._generate_int_term(depth + 1)
        return f"(ite {c} {t} {e})"

    # Elem productions
    def _prod_elem_var(self, depth: int) -> str:
        if not self.vars['Elem']: # Fallback if no elem vars declared
            return self._prod_elem_literal(depth)
        return random.choice(self.vars['Elem'])
    def _prod_elem_literal(self, depth: int) -> str:
        lit = self._generate_elem_literal()
        if lit == "": # Cannot generate a literal for this sort
            # Must use seq.nth to construct an element
            return self._prod_seq_nth(depth)
        return lit
    def _prod_seq_nth(self, depth: int) -> str:
        s = self._generate_seq_term(depth + 1)
        i = self._generate_int_term(depth + 1)
        return f"(seq.nth {s} {i})"
    def _prod_ite_elem(self, depth: int) -> str:
        c = self._generate_bool_term(depth + 1)
        t = self._generate_elem_term(depth + 1)
        e = self._generate_elem_term(depth + 1)
        return f"(ite {c} {t} {e})"

    def generate(self) -> (str, str):
        """Main generation orchestrator."""
        self._initialize_sorts()
        self._initialize_vars()
        formula = self._generate_bool_term(0)
        return "\n".join(self.decls), formula


def generate_sequences_formula_with_decls() -> (str, str):
    """
    Generates a random, well-typed SMT-LIB formula for the Sequences theory.

    This function implements a random formula generator based on a context-free
    grammar for the theory of sequences. It ensures that all generated
    symbols are declared and that the formula is syntactically correct and
    well-typed.

    Returns:
        A tuple (decls, formula), where:
        - decls (str): A string containing all necessary SMT-LIB declarations
          (declare-sort, declare-const) for the formula.
        - formula (str): A string representing a single Boolean term.
    """
    generator = _FormulaGenerator()
    return generator.generate()