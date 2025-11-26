(assert (forall ((a Int) (b Int)) (= (mod (+ a b) 2) 0)))
(check-sat)
