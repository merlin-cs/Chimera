(declare-const x Int)
(assert (forall ((v Real)) (or (= v 0) (distinct 1 (mod x 3)))))
(check-sat)
