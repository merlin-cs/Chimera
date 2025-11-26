(declare-fun b (Int Real) (Array Int Real))
(assert (forall ((v Real)) (= v (select (b 0 v) 0))))
(check-sat)
