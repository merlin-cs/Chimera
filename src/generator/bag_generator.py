import random
import string

class RandomBagFormulaGenerator:
    def __init__(self, num_vars=3, max_depth=3, seed=None, sort="String"):
        random.seed(seed)
        self.num_vars = num_vars
        self.max_depth = max_depth
        self.sort = sort
        # Pre-generate variable names
        prefix = random.choices(string.ascii_lowercase, k=5)
        self.vars = [f"{''.join(prefix)}{random.randint(1, 1000)}" for i in range(num_vars)]
    
    def declare_symbols(self):
        decls = []
        for v in self.vars:
            decls.append(f"(declare-const {v} (Bag {self.sort}))")
        return "\n".join(decls)
    
    def gen_numeral(self):
        return str(random.randint(0, 5))
    
    def gen_string(self):
        # Simple string of one lowercase letter
        return '"' + random.choice("abcde") + '"'
    
    def gen_elem(self):
        return self.gen_string()
    
    def gen_empty_bag(self):
        return f"(as bag.empty (Bag {self.sort}))"
    
    def gen_bag(self, depth):
        if depth <= 0:
            # base case: var or empty bag
            return random.choice(self.vars + [self.gen_empty_bag()])
        
        constructors = [
            lambda d: random.choice(self.vars),
            lambda d: self.gen_empty_bag(),
            lambda d: f"(bag {self.gen_elem()} {self.gen_numeral()})",
            lambda d: f"(bag.union_disjoint {self.gen_bag(d-1)} {self.gen_bag(d-1)})",
            lambda d: f"(bag.union_max      {self.gen_bag(d-1)} {self.gen_bag(d-1)})",
            lambda d: f"(bag.inter_min      {self.gen_bag(d-1)} {self.gen_bag(d-1)})",
            lambda d: f"(bag.difference_subtract {self.gen_bag(d-1)} {self.gen_bag(d-1)})",
            lambda d: f"(bag.setof          {self.gen_bag(d-1)})"
        ]
        return random.choice(constructors)(depth)
    
    def gen_atom(self, depth):
        choice = random.choice(["eq", "member", "subbag"])
        if choice == "eq":
            return f"(= {self.gen_bag(depth-1)} {self.gen_bag(depth-1)})"
        elif choice == "member":
            return f"(bag.member {self.gen_elem()} {self.gen_bag(depth-1)})"
        else:
            return f"(bag.subbag {self.gen_bag(depth-1)} {self.gen_bag(depth-1)})"
    
    def gen_bool(self, depth):
        if depth <= 0:
            return self.gen_atom(depth)
        
        constructors = [
            lambda d: self.gen_atom(d),
            lambda d: f"(not {self.gen_bool(d-1)})",
            lambda d: f"(and {self.gen_bool(d-1)} {self.gen_bool(d-1)})",
            lambda d: f"(or {self.gen_bool(d-1)} {self.gen_bool(d-1)})",
            lambda d: f"(=> {self.gen_bool(d-1)} {self.gen_bool(d-1)})"
        ]
        return random.choice(constructors)(depth)
    
    def generate(self):
        decls = self.declare_symbols()
        formula = self.gen_bool(self.max_depth)
        # return decls + "\n\n" + f"(assert {formula})\n(check-sat)"
        return decls, formula

def generate_bag_formula_with_decls(num_vars=5, max_depth=5, seed=None, sort="String"):
    """Generate a random SMT-LIB snippet with bag declarations and a random Boolean formula."""
    generator = RandomBagFormulaGenerator(num_vars, max_depth, seed, sort)
    return generator.generate()

# Example usage:
if __name__ == "__main__":
    my_formula = generate_bag_formula_with_decls(num_vars=3, max_depth=3)
    print(my_formula)
