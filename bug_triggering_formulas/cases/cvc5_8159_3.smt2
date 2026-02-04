(assert (forall ((a Real) (b Int) (c Int)) (> 1 (+ (* c b (+ a (/ 0 0))) (ite (< 0 (+ 2 a)) 0.0 (+ a 1.0))))))
(check-sat)
