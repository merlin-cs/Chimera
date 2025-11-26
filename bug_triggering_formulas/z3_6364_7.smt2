(declare-fun d (Int Int) Int)
(declare-fun t (Int Int Real) (Array Int (Array Int Real)))
(assert (forall ((u Int) (v Real)) (= v (select (select (t v (d 1 0) (d 0 u)) 0) 0))))
(check-sat)
