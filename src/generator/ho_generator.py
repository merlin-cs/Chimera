import random

class HOFormulaGenerator:
    def __init__(self, seed=None, max_depth=4, num_custom_sorts=2,
                 max_vars_quant_lambda=3, max_args_app=3,
                 max_terms_connective=3):
        self.random = random.Random(seed)
        self.config = {
            "max_depth": max_depth,
            "num_custom_sorts": num_custom_sorts,
            "max_vars_quant_lambda": max_vars_quant_lambda, # For SortedVar+
            "max_args_app": max_args_app, # For Term* in Application
            "max_terms_connective": max_terms_connective, # For BooleanTerm+ in CoreOp/distinct
            "prob_lambda": 0.15,
            "prob_quantifier": 0.15,
            "prob_let": 0,
            "prob_ite": 0.1,
            "prob_application": 0.5, # Higher chance for applications
            "prob_new_symbol_choice": 0.3, # Chance to declare new vs use existing
        }

        self.s_idx = 0  # Custom sort names
        self.v_idx = 0  # Bound variable names (x0, x1, ...)
        self.c_idx = 0  # Constant names (c0, c1, ...)
        self.f_idx = 0  # Function names (f0, f1, ...)

        self.declarations = []
        self.declared_sort_names = ["Bool", "Int"] # User-defined simple sort names
        # self.symbols: name -> {"sort": sort_obj, "kind": "const"|"fun"}
        # sort_obj can be a string like "Bool" or a tuple ("->", [domain_sorts], range_sort)
        self.symbols = {}

    def _next_sort_name(self):
        # generate a random sort name
        name = f"U{self.s_idx}_{self.random.randint(1000, 9999)}"
        self.s_idx += 1
        return name

    def _next_var_name(self):
        # generate a random variable name
        name = f"x{self.v_idx}_{self.random.randint(1000, 9999)}" # Bound var
        self.v_idx += 1
        return name

    def _next_let_var_name(self):
        name = f"lx{self.v_idx}" # Let-bound var
        self.v_idx += 1
        return name

    def _next_const_name(self):
        # generate a random constant name
        name = f"c{self.c_idx}_{self.random.randint(1000, 9999)}" # Const
        # name = f"k{self.c_idx}" # Changed from 'c' to avoid conflict with SMT commands
        self.c_idx += 1
        return name

    def _next_fun_name(self):
        # generate a random function name
        name = f"fn{self.f_idx}_{self.random.randint(1000, 9999)}" # Function
        # name = f"fn{self.f_idx}" # Changed from 'f'
        self.f_idx += 1
        return name

    def _format_sort(self, sort_obj):
        if isinstance(sort_obj, str):
            return sort_obj
        elif isinstance(sort_obj, tuple) and sort_obj[0] == "->":
            _, domain_sorts, range_sort = sort_obj
            if not domain_sorts: # (-> R) is not standard, should be R for const or (-> () R) for 0-ary fun
                 # This case should ideally be handled by ensuring domain_sorts is never empty for a function sort.
                 # For a constant of function type, its sort is (-> A B), not the function symbol itself.
                 # If it's a 0-ary function, its declaration is (declare-fun f () R) and sort is R.
                 # The (-> ...) sort implies it takes arguments.
                 # Let's assume domain_sorts is non-empty for (-> ...) structure.
                 # SMT-LIB: (-> S1 S2 ... Sn T) where n >= 1.
                 # Our tuple: ("->", [S1...Sn], T)
                return self._format_sort(range_sort) # Should not happen if arity >= 1 for domain
            domain_str = " ".join([self._format_sort(s) for s in domain_sorts])
            return f"(-> {domain_str} {self._format_sort(range_sort)})"
        raise ValueError(f"Unknown sort object: {sort_obj}")

    def _add_declaration(self, decl_str):
        # Simple check for duplicates; a set might be better for many decls
        if decl_str not in self.declarations:
            self.declarations.append(decl_str)

    def _declare_new_sort(self):
        name = self._next_sort_name()
        self._add_declaration(f"(declare-sort {name} 0)")
        if name not in self.declared_sort_names:
            self.declared_sort_names.append(name)
        return name

    def _declare_new_symbol(self, sort_obj, kind="const", preferred_name=None):
        if kind == "fun" and not (isinstance(sort_obj, tuple) and sort_obj[0] == "->"):
            raise ValueError("Function kind must have a function sort object.")

        if preferred_name and preferred_name not in self.symbols:
            name = preferred_name
        elif kind == "fun":
            name = self._next_fun_name()
            while name in self.symbols: name = self._next_fun_name()
        else:
            name = self._next_const_name()
            while name in self.symbols: name = self._next_const_name()

        self.symbols[name] = {"sort": sort_obj, "kind": kind}
        
        if kind == "const":
            formatted_sort = self._format_sort(sort_obj)
            self._add_declaration(f"(declare-const {name} {formatted_sort})")
        elif kind == "fun":
            _, domain_sorts, range_sort = sort_obj
            # For declare-fun, we list domain sorts directly, not as (-> ...)
            domain_str = " ".join([self._format_sort(s) for s in domain_sorts])
            range_str = self._format_sort(range_sort)
            self._add_declaration(f"(declare-fun {name} ({domain_str}) {range_str})")
        return name

    def _generate_random_sort(self, depth, allow_function_sort=True):
        if depth <= 0 or not allow_function_sort or self.random.random() < 0.6 or not self.declared_sort_names:
            return self.random.choice(self.declared_sort_names)
        else:
            # Function sort: (-> S1...Sn R)
            num_domain_sorts = self.random.randint(1, max(1,self.config["max_args_app"] // 2 + 1)) # Ensure at least 1 domain sort
            domain_sorts = [self._generate_random_sort(depth - 1, True) for _ in range(num_domain_sorts)]
            range_sort = self._generate_random_sort(depth - 1, True)
            return ("->", domain_sorts, range_sort)

    def _compare_sorts(self, s1, s2):
        if s1 is None or s2 is None: return True # None means any sort is fine
        if isinstance(s1, str) and isinstance(s2, str):
            return s1 == s2
        if isinstance(s1, tuple) and isinstance(s2, tuple) and s1[0] == "->" and s2[0] == "->":
            if len(s1[1]) != len(s2[1]): return False  # Arity of domain
            if not self._compare_sorts(s1[2], s2[2]): return False # Range sort
            for d1_item, d2_item in zip(s1[1], s2[1]):
                if not self._compare_sorts(d1_item, d2_item): return False
            return True
        return False

    def _get_symbols_by_sort(self, expected_sort_obj, scope, kind_filter=None): # kind_filter can be "const", "fun", "var"
        candidates = []
        # Check local scope (vars)
        for name, sort_obj in reversed(scope): # Check innermost first
            if self._compare_sorts(sort_obj, expected_sort_obj):
                if kind_filter is None or kind_filter == "var":
                     candidates.append(name)
        
        # Check global symbols (consts/funcs)
        for name, info in self.symbols.items():
            if self._compare_sorts(info["sort"], expected_sort_obj):
                if kind_filter is None or info["kind"] == kind_filter:
                    candidates.append(name)
                # If expected_sort is a function sort, and symbol is a const of that function sort
                elif info["kind"] == "const" and isinstance(info["sort"], tuple) and info["sort"][0] == "->" and \
                     self._compare_sorts(info["sort"], expected_sort_obj) and (kind_filter is None or kind_filter == "fun"): # Treat const of func sort as callable
                    candidates.append(name)

        return candidates

    def _generate_identifier_term(self, expected_sort_obj, depth, scope, allow_new_decl=True, force_const_if_new=False):
        # Try to find existing symbol
        kind_filter = None
        if isinstance(expected_sort_obj, tuple) and expected_sort_obj[0] == "->":
            kind_filter = "fun" # Prefer functions or consts of function type
        elif expected_sort_obj is not None:
            kind_filter = "const" # Prefer consts or vars

        candidates = self._get_symbols_by_sort(expected_sort_obj, scope, kind_filter=kind_filter)
        if not candidates and kind_filter == "fun": # If no funcs, check for consts of that func sort
            candidates = self._get_symbols_by_sort(expected_sort_obj, scope, kind_filter="const")
        if not candidates and kind_filter == "const": # If no consts, check for vars
             candidates = self._get_symbols_by_sort(expected_sort_obj, scope, kind_filter="var")
        if not candidates: # Broaden search if specific kind fails
            candidates = self._get_symbols_by_sort(expected_sort_obj, scope, kind_filter=None)


        if candidates and (not allow_new_decl or self.random.random() > self.config["prob_new_symbol_choice"]):
            name = self.random.choice(candidates)
            if name in self.symbols:
                return name, self.symbols[name]["sort"]
            else: # Must be from scope
                for var_name, var_sort in scope:
                    if var_name == name:
                        return name, var_sort
                # Should not be reached if candidates are sourced correctly
                raise RuntimeError(f"Symbol {name} from candidates not found in scope or global symbols.")


        # Declare new symbol if allowed or necessary
        if allow_new_decl:
            actual_sort = expected_sort_obj if expected_sort_obj is not None else self._generate_random_sort(depth)
            is_fun_sort = isinstance(actual_sort, tuple) and actual_sort[0] == "->"
            
            kind = "fun" if is_fun_sort and not force_const_if_new else "const"
            if kind == "fun" and not actual_sort[1]: # 0-ary function (-> R) should be declared as (declare-fun f () R)
                # This is tricky. A 0-ary function's "sort" in SMT-LIB is its return sort.
                # Our internal sort_obj for it is ("->", [], R).
                # Let's ensure _declare_new_symbol handles this.
                pass

            name = self._declare_new_symbol(actual_sort, kind)
            return name, actual_sort
        
        # Fallback if no symbol found and new decl not allowed (should be rare if logic is correct)
        # This might happen if depth is 0 and expected_sort is complex and no matching literal.
        # Forcing a simple Bool/Int if all else fails at depth 0.
        if expected_sort_obj == "Bool": return "true", "Bool"
        if expected_sort_obj == "Int": return str(self.random.randint(0,1)), "Int"
        # If absolutely stuck, declare a default Bool const
        name = self._declare_new_symbol("Bool", "const")
        return name, "Bool"


    def _generate_literal_term(self, expected_sort_obj, depth, scope):
        if expected_sort_obj == "Bool" or (expected_sort_obj is None and self.random.random() < 0.5):
            return self.random.choice(["true", "false"]), "Bool"
        if expected_sort_obj == "Int" or (expected_sort_obj is None and self.random.random() >= 0.5):
            return str(self.random.randint(0, 100)), "Int"
        return None # Cannot generate literal for other sorts or if None was not chosen

    def _generate_application_term(self, expected_sort_obj, depth, scope):
        # (func_term arg1 arg2 ...)
        # 1. Determine function's signature
        # SMT-LIB application must have at least one argument for a function symbol.
        # (f) is only valid if f is a 0-ary function, which is just its name.
        # We will enforce at least one argument in generated applications.
        num_args = self.random.randint(1, self.config["max_args_app"])
        arg_sorts = [self._generate_random_sort(depth - 1, allow_function_sort=True) for _ in range(num_args)]
        
        
        # Determine return sort of the function
        # If expected_sort_obj is provided for the application, the function must return that sort.
        # Otherwise, the function can return any sort.
        return_sort = expected_sort_obj if expected_sort_obj is not None else self._generate_random_sort(depth - 1, allow_function_sort=True)

        func_sort_obj = ("->", arg_sorts, return_sort)

        # 2. Generate function term
        # The function term itself can be an identifier or a more complex term (e.g., a lambda, another app)
        func_term_str, actual_func_sort = self._generate_identifier_term(func_sort_obj, depth - 1, scope, allow_new_decl=True)
        
        if not self._compare_sorts(actual_func_sort, func_sort_obj):
            # This can happen if _generate_term couldn't produce exact func_sort_obj
            # and produced something else (e.g. a const of a different sort).
            # Try to recover by finding/declaring a function of the *actual* func_sort's signature if it's a function sort
            if isinstance(actual_func_sort, tuple) and actual_func_sort[0] == "->":
                arg_sorts = actual_func_sort[1] # Use args from the function we actually got
                return_sort = actual_func_sort[2] # Use return from the function we actually got
            else: # The func_term_str is not a function, cannot apply.
                return None # Failed to generate a callable function term.

        # 3. Generate argument terms
        arg_term_strs = []
        for arg_s in arg_sorts:
            arg_str, _ = self._generate_term(arg_s, depth - 1, scope)
            arg_term_strs.append(arg_str)
        
        app_str = f"({func_term_str} {' '.join(arg_term_strs)})".strip()
        # This check is now redundant as num_args is always >= 1
        # if not arg_term_strs: # Handle (func_term) case
        #     app_str = f"({func_term_str})"

        return app_str, return_sort


    def _generate_lambda_term(self, expected_sort_obj, depth, scope):
        # (lambda ((v1 S1) ... (vk Sk)) body)
        num_vars = self.random.randint(1, self.config["max_vars_quant_lambda"])
        
        new_scope = list(scope)
        sorted_vars_str_list = []
        lambda_arg_sorts = []

        for _ in range(num_vars):
            var_name = self._next_var_name()
            var_sort_obj = self._generate_random_sort(depth - 1, allow_function_sort=True)
            lambda_arg_sorts.append(var_sort_obj)
            new_scope.append((var_name, var_sort_obj))
            sorted_vars_str_list.append(f"({var_name} {self._format_sort(var_sort_obj)})")
        
        sorted_vars_smt_str = " ".join(sorted_vars_str_list)

        # Determine body sort
        # If lambda is expected to be (-> D1..Dn R), then body must be R, and D1..Dn must match lambda_arg_sorts
        lambda_return_sort = None
        if expected_sort_obj and isinstance(expected_sort_obj, tuple) and expected_sort_obj[0] == "->":
            # Check if arity and arg sorts match (simplification: assume they do if arity matches)
            if len(expected_sort_obj[1]) == len(lambda_arg_sorts):
                 # For a more robust check, we'd compare each expected_sort_obj[1][i] with lambda_arg_sorts[i]
                 # and potentially regenerate lambda_arg_sorts or fail.
                 # For now, we proceed and the lambda's actual type will be formed by what we generated.
                lambda_return_sort = expected_sort_obj[2] # Expected return sort for the body

        if lambda_return_sort is None: # Not constrained by expected_sort_obj or mismatch
            lambda_return_sort = self._generate_random_sort(depth -1, allow_function_sort=True)

        body_term_str, actual_body_sort = self._generate_term(lambda_return_sort, depth - 1, new_scope)
        
        actual_lambda_sort = ("->", lambda_arg_sorts, actual_body_sort)
        
        # If expected_sort_obj was provided, we should try to match it.
        # If not self._compare_sorts(actual_lambda_sort, expected_sort_obj) and expected_sort_obj is not None:
            # This indicates a mismatch. For now, we proceed with the actual_lambda_sort.
            # A more sophisticated generator might retry or adjust.

        return f"(lambda ({sorted_vars_smt_str}) {body_term_str})", actual_lambda_sort

    def _generate_quantifier_term(self, depth, scope): # Always returns Bool
        quantifier = self.random.choice(["forall", "exists"])
        num_vars = self.random.randint(1, self.config["max_vars_quant_lambda"])
        
        new_scope = list(scope)
        sorted_vars_str_list = []
        for _ in range(num_vars):
            var_name = self._next_var_name()
            var_sort_obj = self._generate_random_sort(depth - 1, allow_function_sort=True)
            new_scope.append((var_name, var_sort_obj))
            sorted_vars_str_list.append(f"({var_name} {self._format_sort(var_sort_obj)})")
        
        sorted_vars_smt_str = " ".join(sorted_vars_str_list)
        body_term_str, _ = self._generate_term("Bool", depth - 1, new_scope)
        return f"({quantifier} ({sorted_vars_smt_str}) {body_term_str})", "Bool"

    def _generate_let_term(self, expected_sort_obj, depth, scope):
        num_bindings = self.random.randint(1, self.config["max_vars_quant_lambda"]) # Re-use config
        
        new_scope = list(scope)
        var_bindings_str_list = []
        for _ in range(num_bindings):
            var_name = self._next_let_var_name()
            # Term for binding can be of any sort
            binding_term_sort_obj = self._generate_random_sort(depth -1, allow_function_sort=True)
            binding_term_str, actual_binding_term_sort = self._generate_term(binding_term_sort_obj, depth - 1, new_scope) # Use new_scope to allow nested lets to see outer let vars
            
            new_scope.append((var_name, actual_binding_term_sort))
            var_bindings_str_list.append(f"({var_name} {binding_term_str})")

        var_bindings_smt_str = " ".join(var_bindings_str_list)
        
        # Body term's sort should match expected_sort_obj
        body_term_str, actual_body_sort = self._generate_term(expected_sort_obj, depth - 1, new_scope)
        return f"(let ({var_bindings_smt_str}) {body_term_str})", actual_body_sort


    def _generate_ite_term(self, expected_sort_obj, depth, scope):
        cond_str, _ = self._generate_term("Bool", depth - 1, scope)
        then_str, s1 = self._generate_term(expected_sort_obj, depth - 1, scope)
        # Else branch must have the same sort as the then branch
        else_str, s2 = self._generate_term(s1, depth - 1, scope) # ensure else has same sort as then
        
        # The overall sort is s1 (or s2, they should be the same)
        # If expected_sort_obj was None, s1 is the determined sort.
        # If expected_sort_obj was specific, s1 should match it.
        return f"(ite {cond_str} {then_str} {else_str})", s1

    def _generate_connective_term(self, depth, scope, op): # for and, or, =>, xor
        # arity: SMT-LIB: and/or (n>=0), => (n>=2), xor (binary)
        # Grammar: CoreOp B B+ (n>=2), xor B B (binary)
        min_terms = 2
        if op == "xor":
            num_terms = 2
        else: # and, or, =>
            num_terms = self.random.randint(min_terms, self.config["max_terms_connective"])

        terms_str = []
        for _ in range(num_terms):
            t_str, _ = self._generate_term("Bool", depth -1, scope)
            terms_str.append(t_str)
        return f"({op} {' '.join(terms_str)})", "Bool"

    def _generate_equals_term(self, depth, scope): # Results in Bool
        # (= t1 t2) where t1 and t2 have the same sort
        s = self._generate_random_sort(depth - 1, allow_function_sort=True)
        t1_str, _ = self._generate_term(s, depth - 1, scope)
        t2_str, _ = self._generate_term(s, depth - 1, scope)
        return f"(= {t1_str} {t2_str})", "Bool"

    def _generate_distinct_term(self, depth, scope): # Results in Bool
        # (distinct t1 t2 ... tn) where all ti have the same sort, n >= 2
        s = self._generate_random_sort(depth - 1, allow_function_sort=True)
        num_terms = self.random.randint(2, self.config["max_terms_connective"])
        terms_str = []
        for _ in range(num_terms):
            t_str, _ = self._generate_term(s, depth -1, scope)
            terms_str.append(t_str)
        return f"(distinct {' '.join(terms_str)})", "Bool"

    def _generate_term(self, expected_sort_obj, depth, scope):
        # Base case: depth depleted
        if depth <= 0:
            # Try literal first if sort matches
            literal_attempt = self._generate_literal_term(expected_sort_obj, depth, scope)
            if literal_attempt:
                return literal_attempt
            # Fallback to identifier (existing or new const)
            return self._generate_identifier_term(expected_sort_obj, depth, scope, allow_new_decl=True, force_const_if_new=True)

        # Recursive step: choose a production
        # Productions:
        # BooleanTerm specific: "true", "false", "not", CoreOp, "xor", Quantifier
        # Shared: <identifier>, Application, "=", "distinct", "ite", "let"
        # Term specific: <literal (non-bool)>, LambdaExpr
        
        # Build a list of (choice_weight, generation_function_or_value, needs_bool_sort)
        # generation_function_or_value can be a lambda calling the specific generator method
        
        choices = []

        # Literals (Bool, Int)
        if expected_sort_obj == "Bool" or expected_sort_obj is None:
            choices.append((10, lambda: ("true", "Bool")))
            choices.append((10, lambda: ("false", "Bool")))
        if expected_sort_obj == "Int" or expected_sort_obj is None:
             choices.append((10, lambda: (str(self.random.randint(0,100)), "Int")))
        
        # Identifiers
        choices.append((30, lambda: self._generate_identifier_term(expected_sort_obj, depth, scope))) # Higher weight

        # Applications
        if self.random.random() < self.config["prob_application"]:
             choices.append((40, lambda: self._generate_application_term(expected_sort_obj, depth, scope)))
        
        # ITE
        if self.random.random() < self.config["prob_ite"]:
            choices.append((15, lambda: self._generate_ite_term(expected_sort_obj, depth, scope)))

        # LET
        if self.random.random() < self.config["prob_let"]:
            choices.append((15, lambda: self._generate_let_term(expected_sort_obj, depth, scope)))

        # Lambda (can produce function sorts, or if expected_sort_obj is a function sort)
        if self.random.random() < self.config["prob_lambda"] and \
           (isinstance(expected_sort_obj, tuple) and expected_sort_obj[0] == "->" or expected_sort_obj is None):
            choices.append((15, lambda: self._generate_lambda_term(expected_sort_obj, depth, scope)))


        # Boolean specific productions (only if expected_sort_obj is Bool or None)
        if expected_sort_obj == "Bool" or expected_sort_obj is None:
            choices.append((10, lambda: (f"(not {self._generate_term('Bool', depth - 1, scope)[0]})", "Bool")))
            choices.append((10, lambda: self._generate_connective_term(depth, scope, self.random.choice(["and", "or", "=>"]))))
            choices.append((5, lambda: self._generate_connective_term(depth, scope, "xor")))
            choices.append((10, lambda: self._generate_equals_term(depth, scope))) # = results in Bool
            choices.append((5, lambda: self._generate_distinct_term(depth, scope))) # distinct results in Bool
            if self.random.random() < self.config["prob_quantifier"]:
                 choices.append((15, lambda: self._generate_quantifier_term(depth, scope)))
        
        # Filter choices that might not be able to produce expected_sort_obj if it's very specific
        # For now, this is implicitly handled by the generation functions trying to match expected_sort_obj.
        # If a function returns None, it means it couldn't satisfy.

        # Weighted choice (simplified):
        # Shuffle and try until one succeeds. If all fail, fallback.
        self.random.shuffle(choices)
        
        for weight, choice_func in choices: # Weight not used in this simplified try-one model
            attempt = choice_func()
            if attempt is not None:
                term_str, actual_sort = attempt
                if expected_sort_obj is None or self._compare_sorts(actual_sort, expected_sort_obj):
                    return term_str, actual_sort
                # If sort mismatch, but expected_sort_obj was specific, this choice was bad.
                # Continue to try other choices.
        
        # Fallback if all choices failed to produce a matching sort or failed to generate:
        # This means the logic above or the called functions couldn't satisfy expected_sort_obj.
        # Default to a simple identifier or literal that matches, or a new const.
        if expected_sort_obj == "Bool": return "true", "Bool"
        if expected_sort_obj == "Int": return str(self.random.randint(0,1)), "Int"
        
        # If expected_sort_obj is complex or a custom sort, try to declare a const for it.
        if expected_sort_obj is not None:
            name = self._declare_new_symbol(expected_sort_obj, "const")
            return name, expected_sort_obj
            
        # Absolute fallback: a generic Bool constant
        fallback_name = self._declare_new_symbol("Bool", "const")
        return fallback_name, "Bool"


    def generate_smtlib_formula(self, num_asserts=1):
        self.declarations = []
        self.symbols = {}
        self.s_idx = self.v_idx = self.c_idx = self.f_idx = 0
        # Reset declared_sort_names to base + config
        self.declared_sort_names = ["Bool", "Int"]


        self._add_declaration("(set-logic HO_ALL)")
        for _ in range(self.config["num_custom_sorts"]):
            self._declare_new_sort()

        # Pre-declare a few common symbols to ensure generator has building blocks
        if "Int" in self.declared_sort_names and "Bool" in self.declared_sort_names:
            self._declare_new_symbol(("->", ["Int"], "Bool"), "fun", preferred_name="p_int_bool")
            self._declare_new_symbol(("->", ["Bool"], "Bool"), "fun", preferred_name="f_bool_bool")
            self._declare_new_symbol("Int", "const", preferred_name="int_const1")
            self._declare_new_symbol("Bool", "const", preferred_name="bool_const1")
            if len(self.declared_sort_names) > 2: # If custom sorts exist
                custom_s = self.declared_sort_names[2]
                self._declare_new_symbol(("->", [custom_s], "Bool"), "fun", preferred_name="f_custom_bool")


        assert_statements = []
        for i in range(num_asserts):
            # Reset var index for each assert to keep var names somewhat contained, or use a global one
            # self.v_idx = 0 # If resetting per assertion
            term_str, term_sort = self._generate_term("Bool", self.config["max_depth"], [])
            if term_sort != "Bool": # Should not happen if _generate_term works for "Bool"
                # Fallback if something went wrong
                assert_statements.append(self._generate_identifier_term('Bool', 0, [], True)[0])
            else:
                assert_statements.append(term_str)
        
        # The original code returned inside the loop, only ever producing one assert.
        # This joins all generated asserts.
        formula_str = "\n".join(assert_statements)
        return self.declarations, formula_str
    

def produce_smtlib_formula_with_decls(num_asserts=1, seed=None, max_depth=4, num_custom_sorts=1):
    generator = HOFormulaGenerator(seed=seed, max_depth=max_depth, num_custom_sorts=num_custom_sorts)
    return generator.generate_smtlib_formula(num_asserts=num_asserts)
    

if __name__ == '__main__':
    generator = HOFormulaGenerator(seed=42, max_depth=3, num_custom_sorts=1)
    formula = generator.generate_smtlib_formula(num_asserts=1)
    print(formula)
