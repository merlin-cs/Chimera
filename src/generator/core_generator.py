import random
import string
from typing import Tuple, List, Set


class CoreFormulaGenerator:
    """Random formula generator for SMT-LIB Core theory."""
    
    def __init__(self, seed: int = None):
        """Initialize the generator with optional seed for reproducibility."""
        if seed is not None:
            random.seed(seed)
        
        # Track declared symbols to ensure consistency
        self.declared_vars: Set[str] = set()
        self.declared_functions: Set[Tuple[str, int]] = set()  # (name, arity)
        self.used_sorts: Set[str] = set()
        
        # Generator parameters
        self.max_depth = 6
        self.max_terms_per_op = 4
        self.var_probability = 0.3
        self.function_probability = 0.2
        
        # Reserved SMT-LIB keywords that should not be used as variable names
        self.reserved_keywords = {
            "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct", 
            "ite", "let", "forall", "exists", "assert", "check-sat", "get-model",
            "declare-const", "declare-fun", "declare-sort", "set-logic", "exit"
        }
    
    def _generate_symbol_name(self, prefix: str = "") -> str:
        """Generate a random symbol name with at least 5 lowercase letters."""
        while True:
            length = random.randint(5, 10)
            name = prefix + ''.join(random.choices(string.ascii_lowercase, k=length))
            # Ensure we don't generate reserved keywords
            if name not in self.reserved_keywords:
                return name
    
    def _ensure_variables(self, min_count: int = 2) -> None:
        """Ensure we have at least min_count variables declared."""
        while len(self.declared_vars) < min_count:
            var_name = self._generate_symbol_name("var")
            if var_name not in self.declared_vars and var_name not in self.reserved_keywords:
                self.declared_vars.add(var_name)
                self.used_sorts.add("Bool")
    
    def _ensure_functions(self, min_count: int = 1) -> None:
        """Ensure we have at least min_count functions declared."""
        current_count = len(self.declared_functions)
        while current_count < min_count:
            func_name = self._generate_symbol_name("func")
            # Ensure function name is not a reserved keyword
            if func_name not in self.reserved_keywords:
                arity = random.randint(1, 3)
                func_sig = (func_name, arity)
                if func_sig not in self.declared_functions:
                    self.declared_functions.add(func_sig)
                    self.used_sorts.add("Bool")
                    current_count += 1
    
    def _generate_bool_term(self, depth: int = 0) -> str:
        """Generate a boolean term according to the grammar."""
        if depth >= self.max_depth:
            # Force terminals at max depth - only use true/false or existing variables
            if self.declared_vars and random.random() < 0.7:
                return random.choice(list(self.declared_vars))
            return random.choice(["true", "false"])
        
        # Choose production rule
        choices = []
        
        # Always allow boolean literals
        choices.extend(["true", "false"])
        
        if depth < self.max_depth - 1:
            choices.extend([
                "not", "=>", "and", "or", "xor", "=", "distinct", "ite"
            ])
        
        # Add variable and function choices if available
        if self.declared_vars and random.random() < self.var_probability:
            choices.append("variable")
        
        if self.declared_functions and random.random() < self.function_probability:
            choices.append("function")
        
        choice = random.choice(choices)
        
        if choice == "true":
            return "true"
        elif choice == "false":
            return "false"
        elif choice == "variable":
            return random.choice(list(self.declared_vars))
        elif choice == "function":
            func_name, arity = random.choice(list(self.declared_functions))
            args = [self._generate_term(depth + 1) for _ in range(arity)]
            return f"({func_name} {' '.join(args)})"
        elif choice == "not":
            inner = self._generate_bool_term(depth + 1)
            return f"(not {inner})"
        elif choice in ["=>", "and", "or", "xor"]:
            num_terms = random.randint(2, min(self.max_terms_per_op, 4))
            terms = [self._generate_bool_term(depth + 1) for _ in range(num_terms)]
            return f"({choice} {' '.join(terms)})"
        elif choice in ["=", "distinct"]:
            num_terms = random.randint(2, min(self.max_terms_per_op, 3))
            terms = [self._generate_term(depth + 1) for _ in range(num_terms)]
            return f"({choice} {' '.join(terms)})"
        elif choice == "ite":
            condition = self._generate_bool_term(depth + 1)
            then_term = self._generate_term(depth + 1)
            else_term = self._generate_term(depth + 1)
            return f"(ite {condition} {then_term} {else_term})"
        
        # Fallback
        return "true"
    
    def _generate_general_term(self, depth: int = 0) -> str:
        """Generate a general term according to the grammar."""
        if depth >= self.max_depth:
            # Force simple terminals - prefer variables over literals at max depth
            if self.declared_vars and random.random() < 0.8:
                return random.choice(list(self.declared_vars))
            return random.choice(["true", "false"])  # Boolean literals as fallback
        
        choices = []
        
        # Boolean terms are also general terms
        if random.random() < 0.4:
            choices.append("bool")
        
        # Variables
        if self.declared_vars:
            choices.append("variable")
        
        # Function applications
        if self.declared_functions and depth < self.max_depth - 1:
            choices.append("function")
        
        if not choices:
            choices = ["bool"]  # Fallback
        
        choice = random.choice(choices)
        
        if choice == "bool":
            return self._generate_bool_term(depth)
        elif choice == "variable":
            return random.choice(list(self.declared_vars))
        elif choice == "function":
            func_name, arity = random.choice(list(self.declared_functions))
            args = [self._generate_term(depth + 1) for _ in range(arity)]
            return f"({func_name} {' '.join(args)})"
        
        # Fallback
        return random.choice(["true", "false"])
    
    def _generate_term(self, depth: int = 0) -> str:
        """Generate a term (bool-term or general-term)."""
        if random.random() < 0.7:  # Prefer boolean terms
            return self._generate_bool_term(depth)
        else:
            return self._generate_general_term(depth)
    
    def _generate_declarations(self) -> str:
        """Generate SMT-LIB declarations for all used symbols."""
        decls = []
        
        # Declare variables (excluding built-in literals)
        for var in sorted(self.declared_vars):
            if var not in self.reserved_keywords:  # Extra safety check
                decls.append(f"(declare-const {var} Bool)")
        
        # Declare functions (excluding built-in functions)
        for func_name, arity in sorted(self.declared_functions):
            if func_name not in self.reserved_keywords:  # Extra safety check
                if arity == 0:
                    decls.append(f"(declare-const {func_name} Bool)")
                else:
                    arg_sorts = " ".join(["Bool"] * arity)
                    decls.append(f"(declare-fun {func_name} ({arg_sorts}) Bool)")
        
        return "\n".join(decls)
    
    def generate(self) -> Tuple[str, str]:
        """Generate a complete SMT-LIB formula with declarations."""
        # Reset state
        self.declared_vars.clear()
        self.declared_functions.clear()
        self.used_sorts.clear()
        
        # Ensure we have some symbols to work with
        self._ensure_variables(random.randint(2, 5))
        if random.random() < 0.6:  # Sometimes include functions
            self._ensure_functions(random.randint(1, 3))
        
        # Generate the main formula
        formula = self._generate_bool_term()
        
        # Generate declarations
        declarations = self._generate_declarations()
        
        return declarations, formula


def generate_core_formula_with_decls() -> Tuple[str, str]:
    """
    Generate a random Core theory formula with declarations.
    
    Returns:
        Tuple[str, str]: A tuple containing:
            - SMT-LIB2 declarations (sorts, constants, functions)
            - SMT-LIB2 boolean formula (without assert wrapper)
    """
    generator = CoreFormulaGenerator()
    return generator.generate()


# Example usage and testing
if __name__ == "__main__":
    # Generate a few examples
    for i in range(3):
        print(f"\n=== Example {i+1} ===")
        declarations, formula = generate_core_formula_with_decls()
        print("Declarations:")
        print(declarations)
        print("\nFormula:")
        print(formula)
        print()