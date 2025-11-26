(declare-fun v () Real)
(assert (forall ((a Real)) (= 0.0 (* v (mod 1 (to_int (/ 1.0 a)))))))
(assert (= 0.0 (/ 1 1.0 0.0)))
(check-sat)
