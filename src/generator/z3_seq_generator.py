import random
import string
from typing import List, Tuple, Set, Dict


class Z3SeqFormulaGenerator:
    """Generator for random SMT-LIB2 formulas using Z3 Sequence theory."""
    
    def __init__(self, seed: int = None):
        """Initialize the generator with optional random seed."""
        if seed is not None:
            random.seed(seed)
        
        # Track declared symbols to avoid redeclaration
        self.declared_symbols: Dict[str, str] = {}  # symbol_name -> sort
        self.used_symbols: Set[str] = set()
        
        # Base sorts available
        self.base_sorts = ['Int', 'Bool', 'Real', 'String', 'Unicode']
        
        # Control generation depth to avoid infinite recursion
        self.max_depth = 8
        self.current_depth = 0
    
    def _generate_symbol_name(self, prefix: str = "") -> str:
        """Generate a random symbol name with at least 5 lowercase letters."""
        length = random.randint(5, 10)
        letters = ''.join(random.choices(string.ascii_lowercase, k=length))
        
        if prefix:
            symbol = f"{prefix}_{letters}"
        else:
            symbol = letters
            
        # Ensure uniqueness
        counter = 0
        original_symbol = symbol
        while symbol in self.used_symbols:
            counter += 1
            symbol = f"{original_symbol}{counter}"
        
        self.used_symbols.add(symbol)
        return symbol
    
    def _generate_sort(self) -> str:
        """Generate a random sort."""
        if random.random() < 0.7:  # 70% chance for base sorts
            return random.choice(self.base_sorts)
        else:  # 30% chance for sequence sorts
            base_sort = random.choice(self.base_sorts)
            return f"(Seq {base_sort})"
    
    def _declare_variable(self, sort: str) -> str:
        """Declare a new variable of given sort and return its name."""
        var_name = self._generate_symbol_name("var")
        self.declared_symbols[var_name] = sort
        return var_name
    
    def _get_or_create_variable(self, sort: str) -> str:
        """Get existing variable of given sort or create new one."""
        # Look for existing variable of this sort
        matching_vars = [name for name, s in self.declared_symbols.items() if s == sort]
        
        if matching_vars and random.random() < 0.6:  # 60% chance to reuse
            return random.choice(matching_vars)
        else:
            return self._declare_variable(sort)
    
    def _generate_numeral(self) -> str:
        """Generate a random numeral."""
        return str(random.randint(0, 100))
    
    def _generate_string_literal(self) -> str:
        """Generate a random string literal."""
        length = random.randint(1, 8)
        chars = ''.join(random.choices(string.ascii_letters + string.digits + " ", k=length))
        return f'"{chars}"'
    
    def _generate_int_expr(self, depth: int = 0) -> str:
        """Generate a random integer expression."""
        if depth >= self.max_depth or random.random() < 0.3:
            # Base case: numeral or variable
            if random.random() < 0.5:
                return self._generate_numeral()
            else:
                return self._get_or_create_variable("Int")
        
        choice = random.randint(1, 7)
        if choice == 1:
            # seq.len
            seq_expr = self._generate_seq_expr(depth + 1)
            return f"(seq.len {seq_expr})"
        elif choice == 2:
            # Addition
            left = self._generate_int_expr(depth + 1)
            right = self._generate_int_expr(depth + 1)
            return f"(+ {left} {right})"
        elif choice == 3:
            # Subtraction
            left = self._generate_int_expr(depth + 1)
            right = self._generate_int_expr(depth + 1)
            return f"(- {left} {right})"
        elif choice == 4:
            # Multiplication
            left = self._generate_int_expr(depth + 1)
            right = self._generate_int_expr(depth + 1)
            return f"(* {left} {right})"
        elif choice == 5:
            # Division
            left = self._generate_int_expr(depth + 1)
            right = self._generate_int_expr(depth + 1)
            return f"(div {left} {right})"
        elif choice == 6:
            # Modulo
            left = self._generate_int_expr(depth + 1)
            right = self._generate_int_expr(depth + 1)
            return f"(mod {left} {right})"
        else:
            # String length (for string expressions)
            string_expr = self._generate_string_expr(depth + 1)
            return f"(str.len {string_expr})"
    
    def _generate_string_expr(self, depth: int = 0) -> str:
        """Generate a random string expression."""
        if depth >= self.max_depth or random.random() < 0.4:
            # Base case: string literal or variable
            if random.random() < 0.5:
                return self._generate_string_literal()
            else:
                return self._get_or_create_variable("String")
        
        choice = random.randint(1, 6)
        if choice == 1:
            # String concatenation
            count = random.randint(2, 3)
            exprs = [self._generate_string_expr(depth + 1) for _ in range(count)]
            return f"(str.++ {' '.join(exprs)})"
        elif choice == 2:
            # String extraction
            string_expr = self._generate_string_expr(depth + 1)
            start = self._generate_int_expr(depth + 1)
            length = self._generate_int_expr(depth + 1)
            return f"(str.extract {string_expr} {start} {length})"
        elif choice == 3:
            # String at position
            string_expr = self._generate_string_expr(depth + 1)
            pos = self._generate_int_expr(depth + 1)
            return f"(str.at {string_expr} {pos})"
        elif choice == 4:
            # String replace
            string_expr = self._generate_string_expr(depth + 1)
            pattern = self._generate_string_expr(depth + 1)
            replacement = self._generate_string_expr(depth + 1)
            return f"(str.replace {string_expr} {pattern} {replacement})"
        elif choice == 5:
            # String from integer
            int_expr = self._generate_int_expr(depth + 1)
            return f"(str.from_int {int_expr})"
        else:
            # String from code
            int_expr = self._generate_int_expr(depth + 1)
            return f"(str.from_code {int_expr})"
    
    def _generate_seq_expr(self, depth: int = 0) -> str:
        """Generate a random sequence expression."""
        if depth >= self.max_depth or random.random() < 0.3:
            # Base case: sequence variable or string (as sequences)
            if random.random() < 0.6:
                # Generate sequence variable
                base_sort = random.choice(self.base_sorts)
                seq_sort = f"(Seq {base_sort})"
                return self._get_or_create_variable(seq_sort)
            else:
                # String as sequence
                return self._generate_string_expr(depth + 1)
        
        choice = random.randint(1, 8)
        if choice == 1:
            # seq.unit
            base_sort = random.choice(self.base_sorts)
            if base_sort == "Int":
                element = self._generate_int_expr(depth + 1)
            elif base_sort == "String":
                element = self._generate_string_expr(depth + 1)
            else:
                element = self._get_or_create_variable(base_sort)
            return f"(seq.unit {element})"
        elif choice == 2:
            # Empty sequence
            base_sort = random.choice(self.base_sorts)
            seq_sort = f"(Seq {base_sort})"
            return f"(as seq.empty {seq_sort})"
        elif choice == 3:
            # Sequence concatenation
            count = random.randint(2, 3)
            exprs = [self._generate_seq_expr(depth + 1) for _ in range(count)]
            return f"(seq.++ {' '.join(exprs)})"
        elif choice == 4:
            # Sequence extraction
            seq_expr = self._generate_seq_expr(depth + 1)
            start = self._generate_int_expr(depth + 1)
            length = self._generate_int_expr(depth + 1)
            return f"(seq.extract {seq_expr} {start} {length})"
        elif choice == 5:
            # Sequence at position
            seq_expr = self._generate_seq_expr(depth + 1)
            pos = self._generate_int_expr(depth + 1)
            return f"(seq.at {seq_expr} {pos})"
        elif choice == 6:
            # Sequence nth
            seq_expr = self._generate_seq_expr(depth + 1)
            pos = self._generate_int_expr(depth + 1)
            return f"(seq.nth {seq_expr} {pos})"
        elif choice == 7:
            # Sequence replace
            seq_expr = self._generate_seq_expr(depth + 1)
            pattern = self._generate_seq_expr(depth + 1)
            replacement = self._generate_seq_expr(depth + 1)
            return f"(seq.replace {seq_expr} {pattern} {replacement})"
        else:
            # Return a sequence variable as fallback
            base_sort = random.choice(self.base_sorts)
            seq_sort = f"(Seq {base_sort})"
            return self._get_or_create_variable(seq_sort)
    
    def _generate_term(self, depth: int = 0) -> str:
        """Generate a random term."""
        choice = random.randint(1, 4)
        if choice == 1:
            return self._generate_numeral()
        elif choice == 2:
            return self._generate_string_literal()
        elif choice == 3:
            return self._generate_seq_expr(depth)
        else:
            return self._generate_int_expr(depth)
    
    def _generate_boolean_term(self, depth: int = 0) -> str:
        """Generate a random boolean term."""
        if depth >= self.max_depth or random.random() < 0.2:
            # Base case: true, false, or boolean variable
            choice = random.randint(1, 3)
            if choice == 1:
                return "true"
            elif choice == 2:
                return "false"
            else:
                return self._get_or_create_variable("Bool")
        
        choice = random.randint(1, 10)
        if choice == 1:
            # not
            term = self._generate_boolean_term(depth + 1)
            return f"(not {term})"
        elif choice == 2:
            # and
            count = random.randint(2, 3)
            terms = [self._generate_boolean_term(depth + 1) for _ in range(count)]
            return f"(and {' '.join(terms)})"
        elif choice == 3:
            # or
            count = random.randint(2, 3)
            terms = [self._generate_boolean_term(depth + 1) for _ in range(count)]
            return f"(or {' '.join(terms)})"
        elif choice == 4:
            # xor
            left = self._generate_boolean_term(depth + 1)
            right = self._generate_boolean_term(depth + 1)
            return f"(xor {left} {right})"
        elif choice == 5:
            # implication
            left = self._generate_boolean_term(depth + 1)
            right = self._generate_boolean_term(depth + 1)
            return f"(=> {left} {right})"
        elif choice == 6:
            # equality
            left = self._generate_term(depth + 1)
            right = self._generate_term(depth + 1)
            return f"(= {left} {right})"
        elif choice == 7:
            # distinct
            count = random.randint(2, 3)
            terms = [self._generate_term(depth + 1) for _ in range(count)]
            return f"(distinct {' '.join(terms)})"
        elif choice == 8:
            # seq.contains
            seq1 = self._generate_seq_expr(depth + 1)
            seq2 = self._generate_seq_expr(depth + 1)
            return f"(seq.contains {seq1} {seq2})"
        elif choice == 9:
            # seq.prefixof
            seq1 = self._generate_seq_expr(depth + 1)
            seq2 = self._generate_seq_expr(depth + 1)
            return f"(seq.prefixof {seq1} {seq2})"
        else:
            # seq.suffixof
            seq1 = self._generate_seq_expr(depth + 1)
            seq2 = self._generate_seq_expr(depth + 1)
            return f"(seq.suffixof {seq1} {seq2})"
    
    def _generate_declarations(self) -> str:
        """Generate SMT-LIB2 declarations for all used symbols."""
        declarations = []
        
        for symbol, sort in self.declared_symbols.items():
            declarations.append(f"(declare-const {symbol} {sort})")
        
        return '\n'.join(declarations)


def generate_z3_seq_formula_with_decls() -> Tuple[str, str]:
    """
    Generate a random SMT-LIB2 formula using Z3 Sequence theory.
    
    Returns:
        Tuple[str, str]: A tuple containing:
            - First string: SMT-LIB2 declarations for all symbols used in the formula
            - Second string: A single SMT-LIB2 Boolean formula (without assert wrapper)
    """
    generator = Z3SeqFormulaGenerator()
    
    # Generate the boolean formula
    formula = generator._generate_boolean_term()
    
    # Generate declarations for all used symbols
    declarations = generator._generate_declarations()
    
    return declarations, formula


# Example usage and testing
if __name__ == "__main__":
    # Generate a few example formulas
    for i in range(3):
        print(f"=== Example {i+1} ===")
        decls, formula = generate_z3_seq_formula_with_decls()
        print("Declarations:")
        print(decls)
        print("\nFormula:")
        print(formula)
        print()