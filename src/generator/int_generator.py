import random
import string

def generate_int_formula_with_decls(max_depth=3, num_vars=5, var_names=None):
    """
    Generate SMT-LIB2-compliant declarations and a single Boolean formula
    over the Int theory, based on the provided CFG.
    
    Returns:
        decls (str): SMT-LIB2 declarations for Int variables.
        formula (str): A well-formed SMT-LIB2 Boolean term.
    """
    def random_symbol(length=1):
        first_chars = string.ascii_letters
        other_chars = first_chars + string.digits
        name = random.choice(first_chars)
        name += ''.join(random.choice(other_chars) for _ in range(length))
        return name

    if var_names is None:
        var_names = [random_symbol(5) for _ in range(num_vars)]
    
    # Generate declarations
    decls = "\n".join(f"(declare-fun {v} () Int)" for v in var_names)
    
    # Helpers for random selection
    numerals = [str(i) for i in range(0, 10)]
    bool_connectives = ["and", "or", "not", "=>", "xor", "ite"]
    rel_ops = ["<=", "<", ">=", ">"]
    
    def rnd_numeral():
        # avoid leading zeros
        num = random.choice(numerals[1:]) + "".join(random.choice(numerals) for _ in range(random.randint(0,2)))
        return num
    
    def rnd_int_term(depth):
        if depth <= 0 or random.random() < 0.3:
            # base: variable or numeral
            if random.random() < 0.5:
                return random.choice(var_names)
            else:
                # possibly a negated numeral
                num = rnd_numeral()
                return f"(- {num})" if num != "0" and random.random() < 0.3 else num
        
        choice = random.choice([
            "sub", "add", "mul", "div", "mod", "abs"
        ])
        if choice == "abs":
            return f"(abs {rnd_int_term(depth-1)})"
        elif choice == "mod":
            # Ensure exactly two arguments for mod
            terms = [rnd_int_term(depth-1) for _ in range(2)]
            return f"(mod {' '.join(terms)})"
        else:
            op_map = {
                "sub": "-",
                "add": "+",
                "mul": "*",
                "div": "div"
            }
            op = op_map[choice]
            # at least two terms
            terms = [rnd_int_term(depth-1) for _ in range(random.randint(2,3))]
            return f"({op} {' '.join(terms)})"
    
    def rnd_bool_atom(depth):
        choice = random.choice(["eq", "distinct", "rel", "divisible"])
        if choice == "eq":
            return f"(= {rnd_int_term(depth-1)} {rnd_int_term(depth-1)})"
        elif choice == "distinct":
            terms = [rnd_int_term(depth-1) for _ in range(random.randint(2,3))]
            return f"(distinct {' '.join(terms)})"
        elif choice == "divisible":
            n = rnd_numeral().lstrip("0") or "1"
            return f"((_ divisible {n}) {rnd_int_term(depth-1)})"
        else:
            op = random.choice(rel_ops)
            terms = [rnd_int_term(depth-1) for _ in range(random.randint(2,3))]
            return f"({op} {' '.join(terms)})"
    
    def rnd_bool_term(depth):
        if depth <= 0 or random.random() < 0.4:
            return rnd_bool_atom(depth)
        conn = random.choice(bool_connectives)
        if conn == "not":
            return f"(not {rnd_bool_term(depth-1)})"
        elif conn == "ite":
            # (ite cond then else)
            return f"(ite {rnd_bool_term(depth-1)} {rnd_bool_term(depth-1)} {rnd_bool_term(depth-1)})"
        else:
            parts = [rnd_bool_term(depth-1) for _ in range(random.randint(2,3))]
            return f"({conn} {' '.join(parts)})"
    
    formula = rnd_bool_term(max_depth)
    return decls, formula

# Example usage
if __name__ == "__main__":
    decls, formula = generate_int_formula_with_decls()
    print("; Declarations")
    print(decls)
    print("\n; Formula")
    print(formula)
