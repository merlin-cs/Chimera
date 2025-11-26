import random
import string

def random_symbol(min_len=5, max_len=8):
    """Generate a random lowercase ASCII symbol with given length constraints."""
    length = random.randint(min_len, max_len)
    return ''.join(random.choice(string.ascii_lowercase) for _ in range(length))

def generate_array_formula_with_decls():
    # Generate two uninterpreted base sorts
    s1 = random_symbol()
    s2 = random_symbol()
    
    # Declarations for the generated sorts
    decls = f"(declare-sort {s1} 0)\n(declare-sort {s2} 0)\n"
    
    # Generate distinct variable names
    a = random_symbol()
    i = random_symbol()
    j = random_symbol()
    e = random_symbol()
    b = random_symbol()
    
    # Build the array sort
    array_sort = f"(Array {s1} {s2})"
    
    # Define the three theory axioms
    axioms = []
    # Axiom 1: store-select
    axioms.append(
        f"(forall (({a} {array_sort}) ({i} {s1}) ({e} {s2})) "
        f"(= (select (store {a} {i} {e}) {i}) {e}))"
    )
    # Axiom 2: store-select distinct
    axioms.append(
        f"(forall (({a} {array_sort}) ({i} {s1}) ({j} {s1}) ({e} {s2})) "
        f"(=> (distinct {i} {j}) "
        f"(= (select (store {a} {i} {e}) {j}) (select {a} {j}))))"
    )
    # Axiom 3: extensionality
    axioms.append(
        f"(forall (({a} {array_sort}) ({b} {array_sort})) "
        f"(=> (forall (({i} {s1})) (= (select {a} {i}) (select {b} {i}))) "
        f"(= {a} {b})))"
    )
    
    # Randomly select one axiom for the formula
    formula = random.choice(axioms)
    
    return decls, formula

# Example usage
if __name__ == "__main__":
    decls_str, formula_str = generate_array_formula_with_decls()
    print("Declarations:\n", decls_str)
    print("Formula:\n", formula_str)
