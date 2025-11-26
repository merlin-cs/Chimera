(assert (forall ((a Int)) (exists ((b Int)) (and (<= 0 (+ a b)) (<= 0 (mod 1 b))))))
(check-sat)
