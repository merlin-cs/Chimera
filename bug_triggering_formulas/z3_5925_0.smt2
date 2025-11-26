(declare-const x (Array Bool (Array Real Real)))
(declare-fun v () (Array Bool (Array Real Real)))
(assert (forall ((a (Array Real Real))) (distinct true (= x (store v false (store a 0.0 0))))))
(check-sat)
