(declare-const x (Set (-> Bool Bool)))
(assert (@ (set.choose (set.minus x (set.singleton (set.choose (set.complement x))))) (seq.prefixof seq.empty seq.empty)))
(check-sat)
