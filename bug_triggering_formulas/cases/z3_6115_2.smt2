(assert (forall ((a Int) (b Int)) (or (< (+ a b) 2) (< (div 1 a) 0) (> b 0))))
(check-sat)
