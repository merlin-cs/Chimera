import random

class FFFormulaGenerator:
    """
    Generates random SMT-LIB2 formulas for the Finite Fields theory based on a provided EBNF.
    Ensures necessary declarations (define-sort, declare-const) are included.
    """

    def __init__(self,
                 prime_field_orders,
                 max_depth=3,
                 num_vars_per_sort_flavor=2,
                 num_sort_aliases=1,
                 max_n_ary_terms=3,
                 seed=None):
        """
        Initializes the formula generator.

        Args:
            prime_field_orders (list[int]): List of prime numbers to use for field orders.
            max_depth (int): Maximum recursion depth for generating terms.
            num_vars_per_sort_flavor (int): Number of variables to declare per unique sort.
            num_sort_aliases (int): Target number of sort aliases (e.g., (define-sort S1 ...)) to create.
            max_n_ary_terms (int): Maximum number of operands for n-ary operators.
            seed (Optional[int]): Seed for the random number generator for reproducibility.
        """
        if not prime_field_orders:
            raise ValueError("prime_field_orders list cannot be empty.")
        if not all(isinstance(p, int) and p > 1 for p in prime_field_orders): # Basic prime check placeholder
            # A full primality test for all inputs is overkill here, user should provide primes.
            print("Warning: prime_field_orders should contain prime numbers greater than 1.")
        if max_depth < 0:
            raise ValueError("max_depth must be non-negative.")
        if num_vars_per_sort_flavor <= 0:
            raise ValueError("num_vars_per_sort_flavor must be positive.")
        if num_sort_aliases < 0:
            raise ValueError("num_sort_aliases must be non-negative.")
        if max_n_ary_terms < 1:
             raise ValueError("max_n_ary_terms must be at least 1.")


        self.prime_field_orders = prime_field_orders
        self.max_depth = max_depth
        self.num_vars_per_sort_flavor = num_vars_per_sort_flavor
        self.num_sort_aliases_target = num_sort_aliases
        
        self.min_add_mul_terms = 2 # As per grammar: ff.add t1 t2 {t}
        self.max_add_mul_terms = max(self.min_add_mul_terms, max_n_ary_terms)
        
        self.min_bitsum_terms = 2  # ff.bitsum requires at least 2 children
        self.max_bitsum_terms = max(self.min_bitsum_terms, max_n_ary_terms)
        
        self.seed = seed
        self._reset_state()

    def _reset_state(self):
        """Initializes or resets the generator's state for a new formula."""
        if self.seed is not None:
            random.seed(self.seed)

        # Key: sort_str (e.g. "SA1", "(_ FiniteField 3)"), Value: list of var names
        self.vars_by_sort_str = {}
        # Key: alias_name ("SA1"), Value: definition_str ("(_ FiniteField 3)")
        self.sort_aliases = {}     
        
        self.var_counter = 0
        self.sort_alias_name_counter = 0 # To generate unique sort alias names like SA1, SA2
        self.actual_sort_aliases_created = 0 # Counter for created aliases vs target
        
        # Stores (define-sort ...) and (declare-const ...) strings
        self.declarations = []

    def _new_var_name(self):
        self.var_counter += 1
        return f"v{self.var_counter}_{random.randint(1, 1000)}" # Unique var name with random suffix

    def _new_sort_alias_name(self):
        self.sort_alias_name_counter += 1
        random_id = random.randint(1000, 9999)
        return f"FFSort_{random_id}" # Fully random identifier

    def _generate_integer_numeral(self, min_val=-10, max_val=10):
        return str(random.randint(min_val, max_val))

    def _pick_prime_order(self):
        return random.choice(self.prime_field_orders)

    def _get_or_create_sort_context(self):
        """
        Decides the sort context (sort string and its prime order) for a new term or equality.
        This can involve reusing an existing sort alias, creating a new one, or using a direct
        sort definition (e.g., "(_ FiniteField P)").
        It ensures that variables are declared for the chosen sort context.

        Returns:
            tuple[str, int]: (sort_str_to_use_in_smtlib, prime_order_int)
        """
        # Probability to reuse an existing alias if available
        prob_reuse_alias = 0.6
        existing_aliases = list(self.sort_aliases.keys())
        if existing_aliases and random.random() < prob_reuse_alias:
            alias_name = random.choice(existing_aliases)
            definition_str = self.sort_aliases[alias_name]
            # Extract prime P from "(_ FiniteField P)"
            prime_order = int(definition_str.split()[-1][:-1])
            self._ensure_vars_declared_for_sort(alias_name)
            return alias_name, prime_order

        # Probability to create a new sort alias if target not met
        prob_create_new_alias = 0.7
        if self.actual_sort_aliases_created < self.num_sort_aliases_target and \
           random.random() < prob_create_new_alias:
            alias_name = self._new_sort_alias_name()
            prime_order = self._pick_prime_order()
            definition_str = f"(_ FiniteField {prime_order})"
            
            # Only add the definition if this alias doesn't already exist
            if alias_name not in self.sort_aliases:
                self.declarations.append(f"(define-sort {alias_name} () {definition_str})")
                self.sort_aliases[alias_name] = definition_str
                self.actual_sort_aliases_created += 1
            self._ensure_vars_declared_for_sort(alias_name)
            return alias_name, prime_order

        # Default: Use a direct sort definition string (e.g., "(_ FiniteField P)")
        prime_order = self._pick_prime_order()
        direct_sort_str = f"(_ FiniteField {prime_order})"
        self._ensure_vars_declared_for_sort(direct_sort_str)
        return direct_sort_str, prime_order
    
    def _ensure_vars_declared_for_sort(self, sort_str_for_decl):
        """
        Ensures that a minimum number of variables are declared for the given sort string.
        The sort_str_for_decl is the SMT-LIB string used in declarations,
        e.g., an alias "FFSort1" or a direct definition "(_ FiniteField 3)".
        """
        if sort_str_for_decl not in self.vars_by_sort_str:
            self.vars_by_sort_str[sort_str_for_decl] = []
            for _ in range(self.num_vars_per_sort_flavor):
                var_name = self._new_var_name()
                self.declarations.append(f"(declare-const {var_name} {sort_str_for_decl})")
                self.vars_by_sort_str[sort_str_for_decl].append(var_name)

    def _get_random_var_for_sort(self, sort_str_in_use):
        """
        Retrieves a random variable name for the given sort string.
        Assumes _ensure_vars_declared_for_sort has already been called for sort_str_in_use.
        """
        if sort_str_in_use in self.vars_by_sort_str and self.vars_by_sort_str[sort_str_in_use]:
            return random.choice(self.vars_by_sort_str[sort_str_in_use])
        else:
            # This fallback should ideally not be hit if logic is correct.
            self._ensure_vars_declared_for_sort(sort_str_in_use) # Attempt to declare if missed
            if sort_str_in_use in self.vars_by_sort_str and self.vars_by_sort_str[sort_str_in_use]:
                 return random.choice(self.vars_by_sort_str[sort_str_in_use])
            raise Exception(f"CRITICAL: Could not get or create a variable for sort '{sort_str_in_use}'. "
                            f"Known vars: {self.vars_by_sort_str}")


    def _generate_field_term(self, term_sort_str, term_prime_order, current_depth):
        """
        Generates a Finite Field term recursively.

        Args:
            term_sort_str (str): The SMT-LIB string for this term's sort.
            term_prime_order (int): The integer prime order of the field.
            current_depth (int): Current recursion depth.

        Returns:
            str: The SMT-LIB string for the generated field term.
        """
        self._ensure_vars_declared_for_sort(term_sort_str) # Ensure vars for current sort context

        if current_depth >= self.max_depth:
            # At max depth, only allow non-recursive term productions
            term_productions = ["symbol", "as_ffN"]
            weights = [0.6, 0.4] # Favor symbols
        else:
            term_productions = ["symbol", "as_ffN", "ff.add", "ff.mul", "ff.neg", "ff.bitsum"]
            weights = [0.35, 0.25, 0.1, 0.1, 0.1, 0.1] # General weights
        
        chosen_production = random.choices(term_productions, weights=weights, k=1)[0]

        if chosen_production == "symbol":
            return self._get_random_var_for_sort(term_sort_str)
        
        elif chosen_production == "as_ffN":
            # 'N' in 'ffN' is an integer numeral. The SMT-LIB symbol is 'ff<N>'.
            # Its semantics is (N mod p). Generate N that might be outside [0, p-1].
            n_val = self._generate_integer_numeral(min_val=-2 * term_prime_order, 
                                                   max_val=2 * term_prime_order)
            ff_smt_symbol = f"ff{n_val}" # e.g., ff-1, ff0, ff3
            return f"(as {ff_smt_symbol} {term_sort_str})"

        # Recursive productions:
        next_depth = current_depth + 1
        
        if chosen_production == "ff.add":
            num_terms = random.randint(self.min_add_mul_terms, self.max_add_mul_terms)
            terms = [self._generate_field_term(term_sort_str, term_prime_order, next_depth) for _ in range(num_terms)]
            return f"(ff.add {' '.join(terms)})"

        elif chosen_production == "ff.mul":
            num_terms = random.randint(self.min_add_mul_terms, self.max_add_mul_terms)
            terms = [self._generate_field_term(term_sort_str, term_prime_order, next_depth) for _ in range(num_terms)]
            return f"(ff.mul {' '.join(terms)})"

        elif chosen_production == "ff.neg":
            term = self._generate_field_term(term_sort_str, term_prime_order, next_depth)
            return f"(ff.neg {term})"

        elif chosen_production == "ff.bitsum":
            num_terms = random.randint(self.min_bitsum_terms, self.max_bitsum_terms)
            terms = [self._generate_field_term(term_sort_str, term_prime_order, next_depth) for _ in range(num_terms)]
            return f"(ff.bitsum {' '.join(terms)})"
        
        # Fallback, should ideally not be reached if all productions are handled.
        return self._get_random_var_for_sort(term_sort_str)


    def _generate_boolean_term_ff(self):
        """Generates the top-level Boolean term: (= <FieldTerm> <FieldTerm>)."""
        sort_str_for_equality, prime_order_for_equality = self._get_or_create_sort_context()

        term1 = self._generate_field_term(sort_str_for_equality, prime_order_for_equality, 0)
        term2 = self._generate_field_term(sort_str_for_equality, prime_order_for_equality, 0)

        return f"(= {term1} {term2})"

    def generate_formula(self):
        """
        Generates a complete SMT-LIB2 formula string for the Finite Fields theory.
        Includes (set-logic), declarations, an assertion, and (check-sat).

        Returns:
            str: A string containing the SMT-LIB2 formula.
        """
        self._reset_state() # Initialize state, applies seed if set

        boolean_assertion = self._generate_boolean_term_ff()

        script_lines = ["(set-logic QF_FF)"]
        
        # Separate sort definitions from variable declarations
        # Sort definitions must come first in SMT-LIB2
        sort_definitions = []
        var_declarations = []
        
        for decl in self.declarations:
            if decl.startswith("(define-sort"):
                sort_definitions.append(decl)
            else:
                var_declarations.append(decl)
        
        # Remove duplicates while preserving order for sort definitions
        # (first occurrence wins for sort definitions)
        seen_sort_names = set()
        unique_sort_definitions = []
        for sort_def in sort_definitions:
            # Extract sort name from "(define-sort SortName () ...)"
            sort_name = sort_def.split()[1]
            if sort_name not in seen_sort_names:
                unique_sort_definitions.append(sort_def)
                seen_sort_names.add(sort_name)
        
        # Remove duplicate variable declarations and sort
        unique_var_declarations = sorted(list(set(var_declarations)))
        
        # Sort definitions should be sorted by sort name for deterministic output
        unique_sort_definitions.sort()
        
        script_lines.extend(unique_sort_definitions)
        script_lines.extend(unique_var_declarations)
        
        script_lines.append(f"(assert {boolean_assertion})")
        script_lines.append("(check-sat)")
        # script_lines.append("(exit)") # Optional: for scripting solver execution
        
        # Return both the ordered declarations and the boolean assertion
        all_declarations = unique_sort_definitions + unique_var_declarations
        return all_declarations, boolean_assertion


def generate_ff_formula_with_decls(prime_field_orders=[3, 5, 7, 11], max_depth=3, num_vars_per_sort_flavor=3, num_sort_aliases=3, max_n_ary_terms=3, seed=None):
    """
    Generates a random SMT-LIB2 formula for the Finite Fields theory with declarations.

    Args:
        prime_field_orders (list[int]): List of prime numbers to use for field orders.
        max_depth (int): Maximum recursion depth for generating terms.
        num_vars_per_sort_flavor (int): Number of variables to declare per unique sort.
        num_sort_aliases (int): Target number of sort aliases to create.
        max_n_ary_terms (int): Maximum number of operands for n-ary operators.
        seed (Optional[int]): Seed for the random number generator for reproducibility.

    Returns:
        str: The generated SMT-LIB2 formula string.
    """
    generator = FFFormulaGenerator(
        prime_field_orders=prime_field_orders,
        max_depth=max_depth,
        num_vars_per_sort_flavor=num_vars_per_sort_flavor,
        num_sort_aliases=num_sort_aliases,
        max_n_ary_terms=max_n_ary_terms,
        seed=seed
    )
    return generator.generate_formula()

if __name__ == '__main__':
    # Example Usage:
    primes = [3, 5, 7, 11] # Small prime numbers for field orders

    # Generator with default settings and a seed for reproducibility
    generator1 = FFFormulaGenerator(
        prime_field_orders=primes,
        seed=42
    )
    formula1 = generator1.generate_formula()
    print("--- Formula 1 (seed=42) ---")
    print(formula1)
    print("\n")

    # Generator with more complexity
    generator2 = FFFormulaGenerator(
        prime_field_orders=primes,
        max_depth=4,
        num_vars_per_sort_flavor=3,
        num_sort_aliases=2,
        max_n_ary_terms=4,
        seed=123
    )
    formula2 = generator2.generate_formula()
    print("--- Formula 2 (seed=123, more complex) ---")
    print(formula2)
    print("\n")
    
    # Generator aiming for simpler output (shallow depth, fewer aliases)
    generator3 = FFFormulaGenerator(
        prime_field_orders=[3, 5], # Only smaller primes
        max_depth=1,
        num_vars_per_sort_flavor=1,
        num_sort_aliases=0, # No sort aliases
        max_n_ary_terms=2,
        seed=7
    )
    formula3 = generator3.generate_formula()
    print("--- Formula 3 (seed=7, simpler) ---")
    print(formula3)