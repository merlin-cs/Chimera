(assert (forall ((a Int)) (exists ((b Int)) (> 0 (* (+ b b b) (div 1 b))))))
(check-sat)
