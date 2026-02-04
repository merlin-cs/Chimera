(assert (forall ((v Real)) (exists ((x Real)) (forall ((y Real)) (or (< 0 (+ x v)) (<= 0 (mod (+ 1 (mod 2 (to_int v))) (to_int y))))))))
(check-sat)
