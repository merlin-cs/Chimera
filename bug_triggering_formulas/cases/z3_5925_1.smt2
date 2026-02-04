(declare-fun v () (Array Bool Bool))
(assert (forall ((r (Array Bool Bool)) (a (Array (Array Bool Bool) Bool))) (distinct true (select (store (store a v true) r true) (store v false false)))))
(check-sat)
