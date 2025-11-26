import random

class SMTFormulaGenerator:
    def __init__(self, max_depth=3, num_int_vars=3, num_bool_vars=3, num_string_vars=2, 
                 num_set_vars=2, num_tuple_vars=2, num_relation_vars=2,
                 random_seed=None):
        self.max_depth = max_depth
        self.max_vars_config = {
            "Int": num_int_vars, "Bool": num_bool_vars, "String": num_string_vars,
            "Set": num_set_vars, # For (Set BaseSort)
            "Tuple": num_tuple_vars,
            "Relation": num_relation_vars # For (Set (Tuple ...))
        }
        if random_seed is not None:
            random.seed(random_seed)

        self.variable_sort_info_map = {}  # var_name -> SortInfo
        self.var_counters = {}  # prefix -> count
        self.declarations_str = []  # Stores (declare-fun ...) strings

    def _get_var_prefix_and_category(self, sort_str):
        if sort_str == "Bool": return "b", "Bool"
        if sort_str == "Int": return "i", "Int"
        if sort_str == "String": return "str", "String"
        if sort_str.startswith("(Set (Tuple"): return "rel" + str(random.randint(0, 1000)), "Relation"
        if sort_str.startswith("(Set"): return "s" + str(random.randint(0, 1000)), "Set"
        # if sort_str.startswith("(Set"): return "s", "Set"
        if sort_str.startswith("(Tuple"): return "t" + str(random.randint(0, 1000)), "Tuple"
        # if sort_str.startswith("(Tuple") or sort_str == "UnitTuple": return "t", "Tuple"
        return "v" + str(random.randint(0, 1000)), "Other"
        # return "v", "Other"

    def _generate_unique_var_name(self, sort_str):
        prefix, _ = self._get_var_prefix_and_category(sort_str)
        count = self.var_counters.get(prefix, 0) + 1
        self.var_counters[prefix] = count
        return f"{prefix}{count}"

    def _get_or_declare_variable(self, required_sort_info):
        sort_str = required_sort_info['sort_str']
        
        compatible_vars = [
            name for name, s_info in self.variable_sort_info_map.items() 
            if s_info['sort_str'] == sort_str
        ]

        _, category = self._get_var_prefix_and_category(sort_str)
        # Fallback for categories not in max_vars_config (e.g. "Other")
        max_vars_for_category = self.max_vars_config.get(category, 1)


        # Try to reuse if possible and allowed
        if compatible_vars and \
           (len(compatible_vars) >= max_vars_for_category or random.random() < 0.7): # Bias towards reuse
            return random.choice(compatible_vars)

        # Create new variable
        var_name = self._generate_unique_var_name(sort_str)
        
        # Ensure var_name is globally unique before adding (should be by _generate_unique_var_name)
        # This also prevents re-adding to declarations_str if somehow called again for an existing var_name
        # (though current logic should make var_name unique for new declarations)
        if var_name not in self.variable_sort_info_map:
             self.declarations_str.append(f"(declare-fun {var_name} () {sort_str})")
             self.variable_sort_info_map[var_name] = required_sort_info
        return var_name

    # --- Sort Generation (returns SortInfo dict) ---
    def _generate_base_sort_info(self):
        s = random.choice(["Int", "String"]) # Add "Real" if needed
        return {'sort_str': s, 'type': 'base'}

    def _generate_element_sort_info_for_set(self, current_depth):
        # Element of a set can be a base sort or a tuple (for relations).
        # Not allowing (Set (Set ...)) directly.
        if current_depth <= 0 or random.random() < 0.6: # Bias to base sort
            return self._generate_base_sort_info()
        else:
            # Allow tuples as elements of sets (i.e., relations)
            return self._generate_tuple_sort_info(current_depth - 1)

    def _generate_set_sort_info(self, current_depth):
        element_s_info = self._generate_element_sort_info_for_set(current_depth -1)
        
        set_sort_str = f"(Set {element_s_info['sort_str']})"
        is_relation_structurally = (element_s_info['type'] == 'tuple')
        
        relation_arity_sort_infos = None
        if is_relation_structurally:
            relation_arity_sort_infos = element_s_info['component_sort_infos']

        return {
            'sort_str': set_sort_str, 'type': 'set', 
            'element_sort_info': element_s_info,
            'is_relation': is_relation_structurally, 
            'relation_arity_sort_infos': relation_arity_sort_infos
        }

    def _generate_tuple_sort_info(self, current_depth):
        num_components = random.randint(0, 2) # (Tuple) is UnitTuple
        if num_components == 0:
            return {'sort_str': "UnitTuple", 'type': 'tuple', 'component_sort_infos': []}
        
        component_s_infos = []
        for _ in range(num_components):
            # Components of a tuple can be any sort according to grammar: <sort>*
            component_s_infos.append(self._generate_sort_info_recursive(current_depth - 1))
        
        component_sort_strs = [csi['sort_str'] for csi in component_s_infos]
        tuple_sort_str = f"(Tuple {' '.join(component_sort_strs)})"
        
        return {'sort_str': tuple_sort_str, 'type': 'tuple', 'component_sort_infos': component_s_infos}

    def _generate_sort_info_recursive(self, current_depth):
        if current_depth <= 0:
            return self._generate_base_sort_info()

        # Weights guide the distribution of generated sort types
        choices = [
            ('base', 3), ('set', 2), ('tuple', 2)
        ]
        
        chosen_type = random.choices([c[0] for c in choices], weights=[c[1] for c in choices], k=1)[0]

        if chosen_type == "base":
            return self._generate_base_sort_info()
        elif chosen_type == "set":
            return self._generate_set_sort_info(current_depth - 1)
        elif chosen_type == "tuple":
            return self._generate_tuple_sort_info(current_depth - 1)
        return self._generate_base_sort_info() # Fallback

    # --- Literal Generation ---
    def _generate_literal(self, sort_str):
        if sort_str == "Int": return str(random.randint(-20, 20))
        if sort_str == "String":
            length = random.randint(1, 4)
            chars = "abcdefghijklmnopqrstuvwxyz0123456789"
            s = "".join(random.choice(chars) for _ in range(length))
            return f'"{s}"'
        return None # Should be called for appropriate sorts

    # --- Term Generation Functions ---
    # Each returns (term_str, sort_info_dict)

    def _generate_smt_bool_term(self, current_depth):
        bool_s_info = {'sort_str': 'Bool', 'type': 'bool'}
        if current_depth <= 0:
            choice = random.choice(["literal", "variable"])
            if choice == "literal": return random.choice(["true", "false"]), bool_s_info
            return self._get_or_declare_variable(bool_s_info), bool_s_info

        rules = [
            "literal_tf", "variable", "not", "n_ary_op", "equals", "distinct", "ite_bool",
            "set_member", "set_subset", "set_is_empty", "set_is_singleton"
        ]
        rule = random.choice(rules)

        if rule == "literal_tf": return random.choice(["true", "false"]), bool_s_info
        if rule == "variable": return self._get_or_declare_variable(bool_s_info), bool_s_info
        if rule == "not":
            t, _ = self._generate_smt_bool_term(current_depth - 1)
            return f"(not {t})", bool_s_info
        if rule == "n_ary_op":
            op = random.choice(["and", "or", "xor", "=>"])
            num_args = random.randint(2, 3)
            args = [self._generate_smt_bool_term(current_depth - 1)[0] for _ in range(num_args)]
            return f"({op} {' '.join(args)})", bool_s_info
        if rule == "equals":
            t1_str, t1_s_info = self._generate_generic_term(current_depth - 1)
            t2_str, _ = self._generate_generic_term(current_depth - 1, target_s_info=t1_s_info)
            return f"(= {t1_str} {t2_str})", bool_s_info
        if rule == "distinct":
            num_args = random.randint(2, 3)
            t1_str, t1_s_info = self._generate_generic_term(current_depth - 1)
            args = [t1_str] + [self._generate_generic_term(current_depth - 1, target_s_info=t1_s_info)[0] for _ in range(num_args - 1)]
            return f"(distinct {' '.join(args)})", bool_s_info
        if rule == "ite_bool":
            c, _ = self._generate_smt_bool_term(current_depth - 1)
            th, _ = self._generate_smt_bool_term(current_depth - 1)
            el, _ = self._generate_smt_bool_term(current_depth - 1)
            return f"(ite {c} {th} {el})", bool_s_info
        if rule == "set_member":
            set_t_str, set_s_info = self._generate_set_term(current_depth - 1)
            elem_s_info = set_s_info['element_sort_info']
            mem_t_str, _ = self._generate_generic_term(current_depth - 1, target_s_info=elem_s_info)
            return f"(set.member {mem_t_str} {set_t_str})", bool_s_info
        if rule == "set_subset":
            s1_str, s1_s_info = self._generate_set_term(current_depth - 1)
            s2_str, _ = self._generate_set_term(current_depth - 1, required_set_s_info=s1_s_info)
            return f"(set.subset {s1_str} {s2_str})", bool_s_info
        if rule == "set_is_empty":
            set_t_str, _ = self._generate_set_term(current_depth - 1)
            return f"(set.is_empty {set_t_str})", bool_s_info
        if rule == "set_is_singleton":
            set_t_str, _ = self._generate_set_term(current_depth - 1)
            return f"(set.is_singleton {set_t_str})", bool_s_info
        
        return random.choice(["true", "false"]), bool_s_info # Fallback

    def _generate_generic_term(self, current_depth, target_s_info=None):
        if target_s_info:
            s_type = target_s_info['type']
            if s_type == 'bool': return self._generate_smt_bool_term(current_depth)
            if s_type == 'set': return self._generate_set_term(current_depth, required_set_s_info=target_s_info)
            if s_type == 'tuple': return self._generate_tuple_term(current_depth, required_tuple_s_info=target_s_info)
            if s_type == 'base': return self._generate_element_like_term(current_depth, required_element_s_info=target_s_info)
            raise ValueError(f"Unknown target sort type: {s_type}")
        else: # No target sort, generate a non-set, non-bool term (suitable for set elements)
            s_info = self._generate_base_sort_info() if random.random() < 0.6 else self._generate_tuple_sort_info(max(0,current_depth -1))
            return self._generate_generic_term(current_depth, target_s_info=s_info)

    def _generate_element_like_term(self, current_depth, required_element_s_info):
        sort_str = required_element_s_info['sort_str']
        if current_depth <= 0:
            options = ["variable"]
            if sort_str in ["Int", "String"]: options.append("literal")
            choice = random.choice(options)
            if choice == "variable": return self._get_or_declare_variable(required_element_s_info), required_element_s_info
            return self._generate_literal(sort_str), required_element_s_info

        rules = ["variable", "ite"]
        if sort_str in ["Int", "String"]: rules.append("literal")
        if sort_str == "Int": rules.append("set_card")
        # tuple.select can produce any base sort. Add if desired, carefully.
        # For simplicity, tuple.select is omitted here but can be added similarly to _generate_set_term's rel.product
        # by finding/creating a tuple with the required_element_s_info as a component.
        
        choice = random.choice(rules)

        if choice == "variable": return self._get_or_declare_variable(required_element_s_info), required_element_s_info
        if choice == "literal": return self._generate_literal(sort_str), required_element_s_info
        if choice == "ite":
            c, _ = self._generate_smt_bool_term(current_depth - 1)
            th, _ = self._generate_element_like_term(current_depth - 1, required_element_s_info)
            el, _ = self._generate_element_like_term(current_depth - 1, required_element_s_info)
            return f"(ite {c} {th} {el})", required_element_s_info
        if choice == "set_card" and sort_str == "Int": # set.card returns Int
            set_t_str, _ = self._generate_set_term(current_depth - 1) # Any set type
            return f"(set.card {set_t_str})", required_element_s_info
        
        # Fallback
        return self._get_or_declare_variable(required_element_s_info), required_element_s_info


    def _generate_set_term(self, current_depth, required_set_s_info=None):
        actual_set_s_info = required_set_s_info or self._generate_set_sort_info(current_depth)
        element_s_info = actual_set_s_info['element_sort_info']
        is_structurally_relation = actual_set_s_info.get('is_relation', False)

        if current_depth <= 0:
            choice = random.choice(["variable", "empty_set"])
            if choice == "variable": return self._get_or_declare_variable(actual_set_s_info), actual_set_s_info
            return f"(as set.empty {actual_set_s_info['sort_str']})", actual_set_s_info

        rules = ["variable", "set_union", "set_inter", "set_minus", "empty_set", 
                   "set_singleton", "set_insert", "set_complement", "set_universe", "ite_set"]
        
        # Only add relation operations if this is actually a relation (set of tuples)
        if is_structurally_relation and element_s_info['type'] == 'tuple':
            rules.extend(["rel_transpose", "rel_join"])
            
            # Only add tclosure for binary relations with same component types (homogeneous)
            if (len(element_s_info.get('component_sort_infos', [])) == 2 and
                element_s_info['component_sort_infos'][0]['sort_str'] == element_s_info['component_sort_infos'][1]['sort_str']):
                rules.append("rel_tclosure")
                
            # Only add product for binary tuple results
            rules.append("rel_product_if_binary_rel")
        
        choice = random.choice(rules)

        if choice == "variable": return self._get_or_declare_variable(actual_set_s_info), actual_set_s_info
        if choice == "empty_set": return f"(as set.empty {actual_set_s_info['sort_str']})", actual_set_s_info
        if choice == "set_universe": return f"(as set.universe {actual_set_s_info['sort_str']})", actual_set_s_info
        if choice in ["set_union", "set_inter", "set_minus"]:
            op = choice.replace("_", ".")
            t1, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            t2, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"({op} {t1} {t2})", actual_set_s_info
        if choice == "set_singleton":
            elem_t, _ = self._generate_generic_term(current_depth - 1, target_s_info=element_s_info)
            return f"(set.singleton {elem_t})", actual_set_s_info
        if choice == "set_insert":
            num_inserts = random.randint(1,2)
            elems_str = [self._generate_generic_term(current_depth - 1, target_s_info=element_s_info)[0] for _ in range(num_inserts)]
            set_arg_str, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"(set.insert {' '.join(elems_str)} {set_arg_str})", actual_set_s_info
        if choice == "set_complement":
            t, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"(set.complement {t})", actual_set_s_info
        if choice == "ite_set":
            c, _ = self._generate_smt_bool_term(current_depth - 1)
            th, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            el, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"(ite {c} {th} {el})", actual_set_s_info
        
        # Relation operations - now with proper guards
        if choice == "rel_transpose" and is_structurally_relation and element_s_info['type'] == 'tuple':
            arg_set, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"(rel.transpose {arg_set})", actual_set_s_info
            
        if (choice == "rel_tclosure" and is_structurally_relation and element_s_info['type'] == 'tuple' and 
            len(element_s_info.get('component_sort_infos', [])) == 2 and
            element_s_info['component_sort_infos'][0]['sort_str'] == element_s_info['component_sort_infos'][1]['sort_str']):
            # Only apply tclosure to homogeneous binary relations (same type for both components)
            arg_set, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
            return f"(rel.tclosure {arg_set})", actual_set_s_info
            
        if choice == "rel_join" and is_structurally_relation and element_s_info['type'] == 'tuple':
            # For join, we need compatible relation types
            # rel.join R1 R2 requires:
            # - R1 is (Set (Tuple T1 ... Tn X))
            # - R2 is (Set (Tuple X U1 ... Um))
            # - Result is (Set (Tuple T1 ... Tn U1 ... Um))
            
            # For simplicity, let's only do joins between binary relations of the form:
            # R1: (Set (Tuple A B)) and R2: (Set (Tuple B C)) -> Result: (Set (Tuple A C))
            
            component_infos = element_s_info.get('component_sort_infos', [])
            if len(component_infos) >= 2:  # Only allow join for non-nullary relations (at least binary)
                # This is a binary or higher-arity relation (Set (Tuple A B ...))
                # We need to find/create another binary relation (Set (Tuple B C))
                # where the second component of this relation matches the first component of the other
                
                first_type = component_infos[0]['sort_str']   # A
                second_type = component_infos[1]['sort_str']  # B
                
                # Create a compatible relation (Set (Tuple B C)) where C is a random base type
                third_type_info = self._generate_base_sort_info()
                third_type = third_type_info['sort_str']  # C
                
                # Create the second relation type (Set (Tuple B C))
                second_rel_element_info = {
                    'sort_str': f"(Tuple {second_type} {third_type})",
                    'type': 'tuple',
                    'component_sort_infos': [
                        {'sort_str': second_type, 'type': 'base'},
                        third_type_info
                    ]
                }
                
                second_rel_info = {
                    'sort_str': f"(Set (Tuple {second_type} {third_type}))",
                    'type': 'set',
                    'element_sort_info': second_rel_element_info,
                    'is_relation': True
                }
                
                # Generate the first relation (of the required type)
                r1, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
                # Generate the second relation (of the compatible type)
                r2, _ = self._generate_set_term(current_depth - 1, required_set_s_info=second_rel_info)
                
                # The result type should be (Set (Tuple A C))
                result_element_info = {
                    'sort_str': f"(Tuple {first_type} {third_type})",
                    'type': 'tuple',
                    'component_sort_infos': [
                        {'sort_str': first_type, 'type': 'base'},
                        third_type_info
                    ]
                }
                
                result_set_info = {
                    'sort_str': f"(Set (Tuple {first_type} {third_type}))",
                    'type': 'set',
                    'element_sort_info': result_element_info,
                    'is_relation': True
                }
                
                return f"(rel.join {r1} {r2})", result_set_info
            else:
                # For nullary relations (empty tuples), fall back to a different operation
                # since join requires non-nullary relations
                t1, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
                t2, _ = self._generate_set_term(current_depth - 1, required_set_s_info=actual_set_s_info)
                return f"(set.union {t1} {t2})", actual_set_s_info


    def _generate_tuple_term(self, current_depth, required_tuple_s_info=None):
        actual_tuple_s_info = required_tuple_s_info or self._generate_tuple_sort_info(current_depth)
        component_s_infos = actual_tuple_s_info['component_sort_infos']

        if current_depth <= 0:
            if not component_s_infos: return "(tuple)", actual_tuple_s_info # UnitTuple literal
            return self._get_or_declare_variable(actual_tuple_s_info), actual_tuple_s_info

        rules = ["variable", "literal_tuple", "ite_tuple"]
        choice = random.choice(rules)

        if choice == "variable": return self._get_or_declare_variable(actual_tuple_s_info), actual_tuple_s_info
        if choice == "literal_tuple":
            if not component_s_infos: return "(tuple)", actual_tuple_s_info
            elems_str = [self._generate_generic_term(current_depth - 1, target_s_info=csi)[0] for csi in component_s_infos]
            return f"(tuple {' '.join(elems_str)})", actual_tuple_s_info
        if choice == "ite_tuple":
            c, _ = self._generate_smt_bool_term(current_depth - 1)
            th, _ = self._generate_tuple_term(current_depth - 1, required_tuple_s_info=actual_tuple_s_info)
            el, _ = self._generate_tuple_term(current_depth - 1, required_tuple_s_info=actual_tuple_s_info)
            return f"(ite {c} {th} {el})", actual_tuple_s_info
        
        # Fallback
        if not component_s_infos: return "(tuple)", actual_tuple_s_info
        return self._get_or_declare_variable(actual_tuple_s_info), actual_tuple_s_info

    def generate_formula_str(self):
        self.variable_sort_info_map.clear()
        self.var_counters.clear()
        self.declarations_str = []

        assertion_term, _ = self._generate_smt_bool_term(self.max_depth)
        
        unique_declarations = sorted(list(set(self.declarations_str)))

        return "\n".join(unique_declarations) + \
               f"\n(assert {assertion_term})\n(check-sat)"
    
    def generate_formula_pair(self):
        self.variable_sort_info_map.clear()
        self.var_counters.clear()
        self.declarations_str = []

        assertion_term, _ = self._generate_smt_bool_term(self.max_depth)
        
        unique_declarations = sorted(list(set(self.declarations_str)))

        return unique_declarations, assertion_term

def produce_smt_formula_with_decls(max_depth=5, num_int_vars=3, num_bool_vars=3, num_string_vars=3, num_set_vars=3, num_tuple_vars=3, num_relation_vars=3, random_seed=None):
    generator = SMTFormulaGenerator(
        max_depth=max_depth, 
        num_int_vars=num_int_vars, 
        num_bool_vars=num_bool_vars,
        num_string_vars=num_string_vars,
        num_set_vars=num_set_vars,
        num_tuple_vars=num_tuple_vars,
        num_relation_vars=num_relation_vars,
        random_seed=random_seed
    )
    return generator.generate_formula_pair()


if __name__ == '__main__':
    # Example Usage:
    generator = SMTFormulaGenerator(
        max_depth=3, 
        num_int_vars=2, 
        num_bool_vars=2,
        num_string_vars=1,
        num_set_vars=1,    # Sets of base types
        num_tuple_vars=1,
        num_relation_vars=1, # Sets of tuples
        random_seed=42 # For reproducibility
    )
    formula = generator.generate_formula_str()
    print(formula)

    print("\n--- Another example with different parameters ---")
    generator_complex = SMTFormulaGenerator(max_depth=4, num_int_vars=3, num_bool_vars=3, random_seed=123)
    formula_complex = generator_complex.generate_formula_str()
    print(formula_complex)