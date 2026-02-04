(assert (forall ((a Int) (b Int)) (distinct 0 (mod (+ a (mod b 3)) 2))))
(check-sat)
