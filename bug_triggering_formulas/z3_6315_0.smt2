(declare-fun v () (Array Bool (Array Int Bool)))
(declare-fun a () (Array Bool (Array Int Bool)))
(assert (forall ((r (Array Int Bool))) (distinct a (store v false (store r 0 true)))))
(check-sat)
