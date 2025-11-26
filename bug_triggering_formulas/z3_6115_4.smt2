(assert (forall ((a Int)) (< (* (mod 2 (+ a 11)) 3) (mod 1 a))))
(check-sat)
