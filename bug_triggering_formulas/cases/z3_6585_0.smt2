(assert (forall ((r Real) (a Real)) (xor (= 0 (/ 1 a)) (< 0.0 (* a r)) (< 0.0 (/ 1 (/ 1.0 0.0))))))
(check-sat)
