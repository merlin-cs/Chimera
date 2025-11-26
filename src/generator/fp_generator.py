import random
import string
from typing import Tuple, List, Set, Dict

class FPFormulaGenerator:
    """Random formula generator for SMT-LIB FloatingPoint theory."""
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        """Reset generator state for a new formula."""
        self.declarations = []
        self.used_symbols = set()
        self.fp_variables_by_sort = {}  # sort_string -> [variable_names]
        self.real_variables = []
        self.max_depth = 3
        self.current_depth = 0
        self.available_sorts = []  # Track available FP sorts
    
    def generate_symbol(self, prefix: str = "") -> str:
        """Generate a unique symbol name with at least 5 lowercase letters."""
        while True:
            # Generate 5-10 random lowercase letters
            length = random.randint(5, 10)
            name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
            if name not in self.used_symbols:
                self.used_symbols.add(name)
                return name
    
    def generate_numeral_greater_than_0(self) -> str:
        """Generate a numeral > 0."""
        return str(random.randint(1, 64))
    
    def generate_numeral_greater_than_1(self) -> str:
        """Generate a numeral > 1."""
        return str(random.randint(2, 64))
    
    def generate_decimal(self) -> str:
        """Generate a decimal number."""
        integer_part = random.randint(0, 999)
        decimal_part = random.randint(1, 999)
        return f"{integer_part}.{decimal_part}"
    
    def generate_floating_point_sort(self) -> str:
        """Generate a FloatingPoint sort."""
        # Use predefined standard sorts more often for consistency
        choices = ['Float16', 'Float32', 'Float64', 'Float128']
        if random.random() < 0.2:  # 20% chance for custom sort
            eb = self.generate_numeral_greater_than_1()
            sb = self.generate_numeral_greater_than_1()
            return f"(_ FloatingPoint {eb} {sb})"
        else:
            return random.choice(choices)
    
    def get_consistent_fp_sort(self) -> str:
        """Get a consistent FloatingPoint sort, preferring existing ones."""
        if self.available_sorts and random.random() < 0.7:  # 70% chance to reuse existing sort
            return random.choice(self.available_sorts)
        else:
            new_sort = self.generate_floating_point_sort()
            if new_sort not in self.available_sorts:
                self.available_sorts.append(new_sort)
            return new_sort
    
    def generate_rounding_mode(self) -> str:
        """Generate a rounding mode."""
        modes = [
            'roundNearestTiesToEven', 'RNE',
            'roundNearestTiesToAway', 'RNA',
            'roundTowardPositive', 'RTP',
            'roundTowardNegative', 'RTN',
            'roundTowardZero', 'RTZ'
        ]
        return random.choice(modes)
    
    def generate_bit_sequence(self, length: int) -> str:
        """Generate a binary bit sequence of given length."""
        return ''.join(random.choices(['0', '1'], k=length))
    
    def generate_hex_sequence(self, length: int) -> str:
        """Generate a hex sequence of given length."""
        hex_digits = '0123456789ABCDEFabcdef'
        return ''.join(random.choices(hex_digits, k=length))
    
    def generate_bitvec_literal_1_bit(self) -> str:
        """Generate a 1-bit BitVec literal."""
        return random.choice(['#b0', '#b1'])
    
    def generate_bitvec_literal_eb_bits(self, eb: int) -> str:
        """Generate an eb-bit BitVec literal."""
        return f"#b{self.generate_bit_sequence(eb)}"
    
    def generate_bitvec_literal_i_bits(self, i: int) -> str:
        """Generate an i-bit BitVec literal."""
        return f"#b{self.generate_bit_sequence(i)}"
    
    def generate_bitvec_literal_m_bits(self, m: int) -> str:
        """Generate an m-bit BitVec literal."""
        if random.choice([True, False]) and m % 4 == 0:
            # Use hex format if m is divisible by 4
            return f"#x{self.generate_hex_sequence(m // 4)}"
        else:
            return f"#b{self.generate_bit_sequence(m)}"
    
    def get_sort_dimensions(self, sort_str: str) -> Tuple[int, int]:
        """Extract eb and sb from a FloatingPoint sort string."""
        if sort_str == 'Float16':
            return 5, 11
        elif sort_str == 'Float32':
            return 8, 24
        elif sort_str == 'Float64':
            return 11, 53
        elif sort_str == 'Float128':
            return 15, 113
        elif sort_str.startswith('(_ FloatingPoint'):
            # Parse "(_ FloatingPoint eb sb)"
            parts = sort_str.split()
            eb = int(parts[2])
            sb = int(parts[3].rstrip(')'))
            return eb, sb
        else:
            # Default fallback
            return 8, 24
    
    def generate_fp_value_constructor(self, target_sort: str = None) -> str:
        """Generate a floating-point value constructor with specific sort."""
        if target_sort is None:
            target_sort = self.get_consistent_fp_sort()
        
        choice = random.choice(['fp', 'special'])
        
        if choice == 'fp':
            eb, sb = self.get_sort_dimensions(target_sort)
            i = sb - 1
            sign_bit = self.generate_bitvec_literal_1_bit()
            exp_bits = self.generate_bitvec_literal_eb_bits(eb)
            sig_bits = self.generate_bitvec_literal_i_bits(i)
            return f"(fp {sign_bit} {exp_bits} {sig_bits})"
        else:
            special_vals = ['+oo', '-oo', '+zero', '-zero', 'NaN']
            special = random.choice(special_vals)
            eb, sb = self.get_sort_dimensions(target_sort)
            return f"(_ {special} {eb} {sb})"
    
    def generate_real_term(self) -> str:
        """Generate a Real term."""
        if not self.real_variables or random.choice([True, False]):
            # Create a new real variable
            var_name = self.generate_symbol("real")
            self.real_variables.append(var_name)
            self.declarations.append(f"(declare-const {var_name} Real)")
            return var_name
        else:
            return random.choice(self.real_variables)
    
    def get_fp_variable_of_sort(self, sort_str: str) -> str:
        """Get or create a FloatingPoint variable of the specified sort."""
        if sort_str not in self.fp_variables_by_sort:
            self.fp_variables_by_sort[sort_str] = []
        
        if not self.fp_variables_by_sort[sort_str] or random.choice([True, False]):
            # Create new variable of this sort
            var_name = self.generate_symbol("fpvar")
            self.fp_variables_by_sort[sort_str].append(var_name)
            self.declarations.append(f"(declare-const {var_name} {sort_str})")
            return var_name
        else:
            return random.choice(self.fp_variables_by_sort[sort_str])
    
    def generate_fp_term(self, target_sort: str = None) -> str:
        """Generate a FloatingPoint term with optional target sort constraint."""
        self.current_depth += 1
        
        if target_sort is None:
            target_sort = self.get_consistent_fp_sort()
        
        if self.current_depth >= self.max_depth:
            # Base case: return a variable or constructor
            if random.choice([True, False]):
                result = self.get_fp_variable_of_sort(target_sort)
            else:
                result = self.generate_fp_value_constructor(target_sort)
            self.current_depth -= 1
            return result
        
        operations = [
            'variable', 'constructor', 'abs', 'neg', 'add', 'sub', 'mul', 'div',
            'fma', 'sqrt', 'rem', 'roundToIntegral', 'min', 'max', 'to_fp'
        ]
        
        op = random.choice(operations)
        result = ""
        
        if op == 'variable':
            result = self.get_fp_variable_of_sort(target_sort)
        
        elif op == 'constructor':
            result = self.generate_fp_value_constructor(target_sort)
        
        elif op == 'abs':
            term = self.generate_fp_term(target_sort)
            result = f"(fp.abs {term})"
        
        elif op == 'neg':
            term = self.generate_fp_term(target_sort)
            result = f"(fp.neg {term})"
        
        elif op in ['add', 'sub', 'mul', 'div']:
            rm = self.generate_rounding_mode()
            term1 = self.generate_fp_term(target_sort)
            term2 = self.generate_fp_term(target_sort)
            result = f"(fp.{op} {rm} {term1} {term2})"
        
        elif op == 'fma':
            rm = self.generate_rounding_mode()
            term1 = self.generate_fp_term(target_sort)
            term2 = self.generate_fp_term(target_sort)
            term3 = self.generate_fp_term(target_sort)
            result = f"(fp.fma {rm} {term1} {term2} {term3})"
        
        elif op in ['sqrt', 'roundToIntegral']:
            rm = self.generate_rounding_mode()
            term = self.generate_fp_term(target_sort)
            result = f"(fp.{op} {rm} {term})"
        
        elif op in ['rem', 'min', 'max']:
            term1 = self.generate_fp_term(target_sort)
            term2 = self.generate_fp_term(target_sort)
            result = f"(fp.{op} {term1} {term2})"
        
        elif op == 'to_fp':
            eb, sb = self.get_sort_dimensions(target_sort)
            conversion_type = random.choice(['bitvec', 'fp', 'real', 'unsigned'])
            
            if conversion_type == 'bitvec':
                m = random.randint(8, 64)
                bv_literal = self.generate_bitvec_literal_m_bits(m)
                result = f"((_ to_fp {eb} {sb}) {bv_literal})"
            elif conversion_type == 'fp':
                rm = self.generate_rounding_mode()
                # Generate FP term of any sort (conversion will change it to target_sort)
                source_sort = self.get_consistent_fp_sort()
                fp_term = self.generate_fp_term(source_sort)
                result = f"((_ to_fp {eb} {sb}) {rm} {fp_term})"
            elif conversion_type == 'real':
                rm = self.generate_rounding_mode()
                real_term = self.generate_real_term()
                result = f"((_ to_fp {eb} {sb}) {rm} {real_term})"
            else:  # unsigned
                rm = self.generate_rounding_mode()
                m = random.randint(8, 64)
                bv_literal = self.generate_bitvec_literal_m_bits(m)
                result = f"((_ to_fp_unsigned {eb} {sb}) {rm} {bv_literal})"
        
        self.current_depth -= 1
        return result
    
    def generate_fp_relational_op(self) -> str:
        """Generate a FloatingPoint relational operation."""
        ops = ['fp.leq', 'fp.lt', 'fp.geq', 'fp.gt', 'fp.eq']
        op = random.choice(ops)
        
        # Ensure both terms have the same sort
        target_sort = self.get_consistent_fp_sort()
        term1 = self.generate_fp_term(target_sort)
        term2 = self.generate_fp_term(target_sort)
        return f"({op} {term1} {term2})"
    
    def generate_fp_is_op(self) -> str:
        """Generate a FloatingPoint classification operation."""
        ops = [
            'fp.isNormal', 'fp.isSubnormal', 'fp.isZero',
            'fp.isInfinite', 'fp.isNaN', 'fp.isNegative', 'fp.isPositive'
        ]
        op = random.choice(ops)
        target_sort = self.get_consistent_fp_sort()
        term = self.generate_fp_term(target_sort)
        return f"({op} {term})"
    
    def generate_boolean_term(self) -> str:
        """Generate a Boolean term (top-level production)."""
        if random.choice([True, False]):
            return self.generate_fp_relational_op()
        else:
            return self.generate_fp_is_op()


def generate_fp_formula_with_decls() -> Tuple[str, str]:
    """
    Generate a random FloatingPoint formula with declarations.
    
    Returns:
        Tuple[str, str]: (declarations, formula)
            - declarations: SMT-LIB2 declarations for all symbols used
            - formula: A Boolean formula in the FloatingPoint theory
    """
    generator = FPFormulaGenerator()
    
    # Generate the Boolean formula
    formula = generator.generate_boolean_term()
    
    # Combine all declarations
    declarations = '\n'.join(generator.declarations)
    
    return declarations, formula


# Example usage and testing
if __name__ == "__main__":
    # Generate a few examples
    for i in range(3):
        print(f"=== Example {i+1} ===")
        decls, formula = generate_fp_formula_with_decls()
        print("Declarations:")
        print(decls)
        print("\nFormula:")
        print(formula)
        print()