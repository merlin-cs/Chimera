(assert (forall ((v Real)) (or (exists ((a Real)) (= 0.0 (/ (* v v) a 0.0))))))
(check-sat)
