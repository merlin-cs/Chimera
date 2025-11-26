import random

class SMTLibDatatypeGenerator:
    def __init__(self,
                 datatypes,
                 tuple_arity=2,
                 num_vars=3,
                 max_depth=3,
                 seed=None):
        """
        datatypes: dict from datatype name to list of constructors,
                   where each constructor is (name, [(sel_name, sel_sort), ...])
        tuple_arity: arity for generated tuples
        num_vars: number of variables per sort
        max_depth: max recursion depth
        seed: random seed for reproducibility
        """
        self.datatypes = datatypes
        self.tuple_arity = tuple_arity
        self.num_vars = num_vars
        self.max_depth = max_depth
        if seed is not None:
            random.seed(seed)

        # collect sorts
        self.sorts = set()
        for dt, ctors in datatypes.items():
            self.sorts.add(dt)
            for _, sels in ctors:
                for _, srt in sels:
                    self.sorts.add(srt)
        self.sorts.add('Int')
        self.sorts.add('Bool')
        self.sorts.add('String')
        
        # Build selector to datatype mapping
        self.selector_to_datatype = {}
        for dt, ctors in datatypes.items():
            for _, sels in ctors:
                for sel_name, sel_sort in sels:
                    self.selector_to_datatype[sel_name] = (dt, sel_sort)
        
        # pre-generate variable names by sort
        self.vars = {s: [f"{s.lower()}_{i}" for i in range(num_vars)] for s in self.sorts}

    def decls(self):
        lines = []
        # declare datatypes - ensure proper formatting
        if self.datatypes:
            dt_list = []
            for dt in self.datatypes:
                dt_list.append(f'({dt} 0)')
            
            all_ctor_strs = []
            # constructors
            for dt, ctors in self.datatypes.items():
                ctor_strs = []
                for ctor, sels in ctors:
                    if sels:
                        sel_str = ' '.join(f'({n} {srt})' for n, srt in sels)
                        ctor_strs.append(f'({ctor} {sel_str})')
                    else:
                        ctor_strs.append(f'({ctor})')
                all_ctor_strs.append(f"({' '.join(ctor_strs)})")
            
            lines.append(f"(declare-datatypes ({' '.join(dt_list)}) ({' '.join(all_ctor_strs)}))")
        
        # declare variables
        for s in self.sorts:
            for v in self.vars[s]:
                lines.append(f"(declare-fun {v} () {s})")
        return '\n'.join(lines)

    def rand_term(self, depth=None, target_sort=None):
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            # choose leaf: constant or var
            if target_sort == 'Int':
                choice = random.choice(['const', 'var'])
                if choice == 'const':
                    return str(random.randint(0, 10))
                else:
                    return random.choice(self.vars['Int'])
            elif target_sort == 'Bool':
                choice = random.choice(['const', 'var'])
                if choice == 'const':
                    return random.choice(['true', 'false'])
                else:
                    return random.choice(self.vars['Bool'])
            elif target_sort == 'String':
                choice = random.choice(['const', 'var'])
                if choice == 'const':
                    return f'"str{random.randint(0,100)}"'
                else:
                    return random.choice(self.vars['String'])
            elif target_sort in self.datatypes:
                return random.choice(self.vars[target_sort])
            else:
                # no target sort specified, choose randomly
                choice = random.choice(['int', 'bool', 'string', 'var'])
                if choice == 'int':
                    return str(random.randint(0, 10))
                if choice == 'bool':
                    return random.choice(['true', 'false'])
                if choice == 'string':
                    return f'"str{random.randint(0,100)}"'
                # var
                s = random.choice(list(self.sorts))
                return random.choice(self.vars[s])
        
        # choose non-leaf - limit tuple operations when we have a specific target sort
        kinds = ['ctor','sel','upd','ite']
        if target_sort is None:
            kinds.extend(['tuple_ctor','tuple_sel','tuple_upd','tuple_proj'])
        
        kind = random.choice(kinds)
        if kind == 'ctor':
            dt = target_sort if target_sort in self.datatypes else random.choice(list(self.datatypes.keys()))
            ctors = self.datatypes[dt]
            ctor, sels = random.choice(ctors)
            args = []
            for _, sel_sort in sels:
                args.append(self.rand_term(depth-1, sel_sort))
            if args:
                return f'({ctor} ' + ' '.join(args) + ')'
            else:
                return f'({ctor})'
        if kind == 'sel':
            # Choose a selector and ensure we apply it to the correct datatype
            if not self.selector_to_datatype:
                return self.rand_term(depth-1, target_sort)
            sel_name, (dt, sel_sort) = random.choice(list(self.selector_to_datatype.items()))
            # If we have a target sort, only use selectors that return that sort
            if target_sort is not None and sel_sort != target_sort:
                return self.rand_term(depth-1, target_sort)
            t = self.rand_term(depth-1, dt)
            return f'({sel_name} {t})'
        if kind == 'upd':
            # Find a selector and its datatype
            if not self.selector_to_datatype:
                return self.rand_term(depth-1, target_sort)
            sel_name, (dt, sel_sort) = random.choice(list(self.selector_to_datatype.items()))
            # If we have a target sort, only use updates that return that sort
            if target_sort is not None and dt != target_sort:
                return self.rand_term(depth-1, target_sort)
            t = self.rand_term(depth-1, dt)
            u = self.rand_term(depth-1, sel_sort)
            return f'((_ update {sel_name}) {t} {u})'
        if kind == 'tuple_ctor':
            args = [self.rand_term(depth-1) for _ in range(self.tuple_arity)]
            return f'(tuple ' + ' '.join(args) + ')'
        if kind == 'tuple_sel':
            i = random.randint(0, self.tuple_arity-1)
            t = self.rand_tuple_term(depth-1)
            return f'((_ tuple.select {i}) {t})'
        if kind == 'tuple_upd':
            i = random.randint(0, self.tuple_arity-1)
            t = self.rand_tuple_term(depth-1)
            u = self.rand_term(depth-1)
            return f'((_ tuple.update {i}) {t} {u})'
        if kind == 'tuple_proj':
            indices = ' '.join(str(random.randint(0, self.tuple_arity-1)) for _ in range(random.randint(1,self.tuple_arity)))
            t = self.rand_tuple_term(depth-1)
            return f'((_ tuple.project {indices}) {t})'
        # ite
        cond = self.rand_bool(depth-1)
        t1 = self.rand_term(depth-1, target_sort)
        t2 = self.rand_term(depth-1, target_sort)
        return f'(ite {cond} {t1} {t2})'

    def rand_tuple_term(self, depth=None):
        """Generate a term that is guaranteed to be a tuple"""
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            args = [self.rand_term(0) for _ in range(self.tuple_arity)]
            return f'(tuple ' + ' '.join(args) + ')'
        
        # Either create a new tuple or use ite with tuple branches
        if random.choice([True, False]):
            args = [self.rand_term(depth-1) for _ in range(self.tuple_arity)]
            return f'(tuple ' + ' '.join(args) + ')'
        else:
            cond = self.rand_bool(depth-1)
            t1 = self.rand_tuple_term(depth-1)
            t2 = self.rand_tuple_term(depth-1)
            return f'(ite {cond} {t1} {t2})'

    def rand_bool(self, depth=None):
        if depth is None:
            depth = self.max_depth
        if depth <= 0:
            # simple compare or var
            choice = random.choice(['const', 'var'])
            if choice == 'const':
                return random.choice(['true', 'false'])
            else:
                return random.choice(self.vars['Bool'])
        
        kinds = ['and','or','not','comp','distinct','tester','ite']
        kind = random.choice(kinds)
        if kind == 'and' or kind == 'or':
            n = random.randint(2,3)
            terms = [self.rand_bool(depth-1) for _ in range(n)]
            return f'({kind} ' + ' '.join(terms) + ')'
        if kind == 'not':
            return f'(not {self.rand_bool(depth-1)})'
        if kind == 'comp':
            # Choose compatible types for comparison
            sort_choice = random.choice(['Int', 'Bool', 'String'] + list(self.datatypes.keys()))
            if sort_choice == 'Int':
                left = self.rand_term(depth-1, 'Int')
                right = self.rand_term(depth-1, 'Int')
                op = random.choice(['=','>','<','>=','<='])
            else:
                left = self.rand_term(depth-1, sort_choice)
                right = self.rand_term(depth-1, sort_choice)
                op = '='  # Only equality for non-numeric types
            return f'({op} {left} {right})'
        if kind == 'distinct':
            # Use same sort for all terms in distinct
            sort_choice = random.choice(['Int', 'Bool', 'String'] + list(self.datatypes.keys()))
            n = random.randint(2,3)
            terms = [self.rand_term(depth-1, sort_choice) for _ in range(n)]
            return f'(distinct ' + ' '.join(terms) + ')'
        if kind == 'tester':
            # Choose a datatype and ensure we apply tester to correct type
            if not self.datatypes:
                return self.rand_bool(depth-1)
            dt = random.choice(list(self.datatypes.keys()))
            ctor = random.choice([ctor for ctor, _ in self.datatypes[dt]])
            t = self.rand_term(depth-1, dt)
            return f'((_ is {ctor}) {t})'
        # ite
        cond = self.rand_bool(depth-1)
        t1 = self.rand_bool(depth-1)
        t2 = self.rand_bool(depth-1)
        return f'(ite {cond} {t1} {t2})'

    def generate(self):
        decls = self.decls()
        formula = self.rand_bool()
        script = decls + '\n(assert ' + formula + ')\n(check-sat)'
        # return script
        return decls, formula
    
    
DATATYPES = {
    'list': [
        ('cons', [('head','Int'), ('tail','list')]),
        ('nil', [])
    ],
    'record': [
        ('rec', [('fname','String'), ('lname','String'), ('id','Int')])
    ]
}

def generate_smtlib_datatype_with_decls(datatypes=DATATYPES,
                                      tuple_arity=2,
                                      num_vars=3,
                                      max_depth=3,
                                      seed=None):
    """
    Generate SMT-LIB script with datatype declarations and a random formula.
    """
    gen = SMTLibDatatypeGenerator(datatypes, tuple_arity, num_vars, max_depth, seed)
    return gen.generate()

if __name__ == "__main__":
    # example usage
    dts = {
        'list': [
            ('cons', [('head','Int'), ('tail','list')]),
            ('nil', [])
        ],
        'record': [
            ('rec', [('fname','String'), ('lname','String'), ('id','Int')])
        ]
    }
    gen = SMTLibDatatypeGenerator(datatypes=dts, tuple_arity=2, num_vars=2, max_depth=3, seed=42)
    print(gen.generate())
