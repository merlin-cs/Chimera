(declare-const a Int)
(declare-const b Int)
(assert (> (to_real (abs b)) (/ (to_real a) (to_real b))))
(check-sat)
