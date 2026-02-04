(assert (exists ((x Real)) (forall ((y Real)) (exists ((z Real)) (and (<= 1 (/ x y)) (= 1 (/ y z y)))))))
(check-sat)
