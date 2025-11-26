import random
import string
from typing import Tuple, List, Dict, Set

class BVFormulaGenerator:
    """Generator for FixedSizeBitVectors theory formulas following SMT-LIB2 syntax."""
    
    def __init__(self, seed=None):
        """Initialize the generator with optional random seed."""
        if seed is not None:
            random.seed(seed)
        
        # Configuration parameters
        self.max_depth = 6
        self.max_width = 32
        self.min_width = 1
        self.max_terms_in_assoc = 4
        
        # Track declared variables and their widths
        self.declared_vars: Dict[str, int] = {}
        self.used_symbols: Set[str] = set()
        
        # Grammar production weights for randomization
        self.bool_term_weights = {
            'const': 0.2,
            'not': 0.1,
            'and': 0.15,
            'or': 0.15,
            'implies': 0.1,
            'equals': 0.15,
            'bvult': 0.1,
            'predop': 0.05
        }
        
        self.bv_term_weights = {
            'literal': 0.3,
            'var': 0.25,
            'concat': 0.1,
            'extract': 0.1,
            'unop': 0.1,
            'binop': 0.1,
            'reduce': 0.05
        }

    def generate_symbol(self, prefix: str = "") -> str:
        """Generate a random symbol name with at least 5 lowercase letters."""
        while True:
            # Generate 5-10 random lowercase letters
            length = random.randint(5, 10)
            name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
            if name not in self.used_symbols:
                self.used_symbols.add(name)
                return name

    def generate_bv_literal(self, width: int) -> str:
        """Generate a bitvector literal of specified width."""
        if random.choice([True, False]):  # Binary literal
            bits = ''.join(random.choices(['0', '1'], k=width))
            return f"#b{bits}"
        else:  # Hex literal (only if width is multiple of 4)
            if width % 4 == 0:
                hex_digits = width // 4
                hex_str = ''.join(random.choices('0123456789ABCDEF', k=hex_digits))
                return f"#x{hex_str}"
            else:
                # Fall back to binary for non-4-multiple widths
                bits = ''.join(random.choices(['0', '1'], k=width))
                return f"#b{bits}"

    def get_or_create_bv_var(self, width: int) -> str:
        """Get an existing variable of given width or create a new one."""
        # Look for existing variable with this width
        candidates = [var for var, w in self.declared_vars.items() if w == width]
        
        if candidates and random.random() < 0.6:  # 60% chance to reuse
            return random.choice(candidates)
        else:
            # Create new variable
            var_name = self.generate_symbol("bv")
            self.declared_vars[var_name] = width
            return var_name

    def generate_bv_term(self, depth: int = 0, target_width: int = None) -> Tuple[str, int]:
        """Generate a bitvector term. Returns (term, width)."""
        if depth >= self.max_depth:
            # Force leaf nodes at max depth
            if target_width:
                if random.choice([True, False]):
                    return self.generate_bv_literal(target_width), target_width
                else:
                    var = self.get_or_create_bv_var(target_width)
                    return var, target_width
            else:
                width = random.randint(self.min_width, self.max_width)
                if random.choice([True, False]):
                    return self.generate_bv_literal(width), width
                else:
                    var = self.get_or_create_bv_var(width)
                    return var, width

        # Choose production based on weights
        choice = random.choices(
            list(self.bv_term_weights.keys()),
            weights=list(self.bv_term_weights.values())
        )[0]

        if choice == 'literal':
            width = target_width if target_width else random.randint(self.min_width, self.max_width)
            return self.generate_bv_literal(width), width
            
        elif choice == 'var':
            width = target_width if target_width else random.randint(self.min_width, self.max_width)
            var = self.get_or_create_bv_var(width)
            return var, width
            
        elif choice == 'concat':
            if target_width:
                # If we have a target width, we need to generate operands that sum to that width
                # Split the target width into two parts
                max_width1 = min(target_width - 1, self.max_width // 2)
                min_width1 = max(1, target_width - self.max_width // 2)
                
                if min_width1 > max_width1:
                    # Can't satisfy target_width with concat, fall back to other operations
                    # Force a literal or variable instead
                    if random.choice([True, False]):
                        return self.generate_bv_literal(target_width), target_width
                    else:
                        var = self.get_or_create_bv_var(target_width)
                        return var, target_width
                
                width1 = random.randint(min_width1, max_width1)
                width2 = target_width - width1
                
                term1, _ = self.generate_bv_term(depth + 1, width1)
                term2, _ = self.generate_bv_term(depth + 1, width2)
                
                return f"(concat {term1} {term2})", target_width
            else:
                # Generate two terms with random widths
                width1 = random.randint(self.min_width, self.max_width // 2)
                width2 = random.randint(self.min_width, self.max_width // 2)
                
                term1, _ = self.generate_bv_term(depth + 1, width1)
                term2, _ = self.generate_bv_term(depth + 1, width2)
                
                return f"(concat {term1} {term2})", width1 + width2
            
        elif choice == 'extract':
            # Generate a term with sufficient width for extraction
            min_source_width = 2 if not target_width else max(2, target_width)
            source_width = random.randint(min_source_width, self.max_width)
            
            term, _ = self.generate_bv_term(depth + 1, source_width)
            
            # Choose extract indices
            if target_width:
                extract_width = target_width
                if extract_width > source_width:
                    extract_width = source_width
            else:
                extract_width = random.randint(1, source_width)
            
            high = random.randint(extract_width - 1, source_width - 1)
            low = high - extract_width + 1
            
            return f"((_ extract {high} {low}) {term})", extract_width
            
        elif choice == 'unop':
            width = target_width if target_width else random.randint(self.min_width, self.max_width)
            op = random.choice(['bvnot', 'bvneg'])
            term, _ = self.generate_bv_term(depth + 1, width)
            return f"({op} {term})", width
            
        elif choice == 'binop':
            width = target_width if target_width else random.randint(self.min_width, self.max_width)
            op = random.choice(['bvand', 'bvor', 'bvadd', 'bvmul', 'bvudiv', 'bvurem', 'bvshl', 'bvlshr'])
            
            term1, _ = self.generate_bv_term(depth + 1, width)
            term2, _ = self.generate_bv_term(depth + 1, width)
            
            return f"({op} {term1} {term2})", width
            
        elif choice == 'reduce':
            width = target_width if target_width else random.randint(self.min_width, self.max_width)
            op = random.choice(['bvand', 'bvor', 'bvadd', 'bvmul'])
            
            num_terms = random.randint(2, self.max_terms_in_assoc)
            terms = []
            for _ in range(num_terms):
                term, _ = self.generate_bv_term(depth + 1, width)
                terms.append(term)
            
            return f"({op} {' '.join(terms)})", width

    def generate_bool_term(self, depth: int = 0) -> str:
        """Generate a Boolean term."""
        if depth >= self.max_depth:
            # Force leaf nodes at max depth
            return random.choice(['true', 'false'])

        # Choose production based on weights
        choice = random.choices(
            list(self.bool_term_weights.keys()),
            weights=list(self.bool_term_weights.values())
        )[0]

        if choice == 'const':
            return random.choice(['true', 'false'])
            
        elif choice == 'not':
            inner = self.generate_bool_term(depth + 1)
            return f"(not {inner})"
            
        elif choice == 'and':
            num_terms = random.randint(2, self.max_terms_in_assoc)
            terms = [self.generate_bool_term(depth + 1) for _ in range(num_terms)]
            return f"(and {' '.join(terms)})"
            
        elif choice == 'or':
            num_terms = random.randint(2, self.max_terms_in_assoc)
            terms = [self.generate_bool_term(depth + 1) for _ in range(num_terms)]
            return f"(or {' '.join(terms)})"
            
        elif choice == 'implies':
            term1 = self.generate_bool_term(depth + 1)
            term2 = self.generate_bool_term(depth + 1)
            return f"(=> {term1} {term2})"
            
        elif choice == 'equals':
            width = random.randint(self.min_width, self.max_width)
            term1, actual_width1 = self.generate_bv_term(depth + 1, width)
            term2, actual_width2 = self.generate_bv_term(depth + 1, width)
            
            # If widths don't match due to operations like concat, regenerate term2 with actual_width1
            if actual_width1 != actual_width2:
                term2, _ = self.generate_bv_term(depth + 1, actual_width1)
            
            return f"(= {term1} {term2})"
            
        elif choice == 'bvult':
            width = random.randint(self.min_width, self.max_width)
            term1, actual_width1 = self.generate_bv_term(depth + 1, width)
            term2, actual_width2 = self.generate_bv_term(depth + 1, width)
            
            # If widths don't match due to operations like concat, regenerate term2 with actual_width1
            if actual_width1 != actual_width2:
                term2, _ = self.generate_bv_term(depth + 1, actual_width1)
            
            return f"(bvult {term1} {term2})"
            
        elif choice == 'predop':
            op = random.choice(['bvuaddo', 'bvsaddo', 'bvumulo', 'bvsmulo', 'bvnego'])
            
            if op == 'bvnego':
                # Unary predicate - treated as taking one argument
                width = random.randint(self.min_width, self.max_width)
                term, _ = self.generate_bv_term(depth + 1, width)
                return f"({op} {term})"
            else:
                # Binary predicates
                width = random.randint(self.min_width, self.max_width)
                term1, actual_width1 = self.generate_bv_term(depth + 1, width)
                term2, actual_width2 = self.generate_bv_term(depth + 1, width)
                
                # If widths don't match due to operations like concat, regenerate term2 with actual_width1
                if actual_width1 != actual_width2:
                    term2, _ = self.generate_bv_term(depth + 1, actual_width1)
                
                return f"({op} {term1} {term2})"

    def generate_declarations(self) -> str:
        """Generate SMT-LIB2 declarations for all used variables."""
        declarations = []
        
        for var_name, width in sorted(self.declared_vars.items()):
            declarations.append(f"(declare-const {var_name} (_ BitVec {width}))")
        
        return '\n'.join(declarations)

    def reset(self):
        """Reset the generator state for a new formula."""
        self.declared_vars.clear()
        self.used_symbols.clear()


def generate_bv_formula_with_decls() -> Tuple[str, str]:
    """
    Generate a random FixedSizeBitVectors formula with declarations.
    
    Returns:
        Tuple[str, str]: (declarations, formula)
            - declarations: SMT-LIB2 variable declarations
            - formula: A single Boolean formula term
    """
    generator = BVFormulaGenerator()
    
    # Generate the main Boolean formula
    formula = generator.generate_bool_term()
    
    # Generate declarations for all used variables
    declarations = generator.generate_declarations()
    
    return declarations, formula


# Example usage and testing
if __name__ == "__main__":
    # Generate a few example formulas
    for i in range(3):
        print(f"=== Example {i+1} ===")
        decls, formula = generate_bv_formula_with_decls()
        
        print("Declarations:")
        print(decls)
        print("\nFormula:")
        print(formula)
        print()