(declare-const x4 Int)
(declare-const x (Set Int))
(assert (seq.prefixof (seq.unit 0) (seq.unit (* x4 (set.card x)))))
(check-sat)
