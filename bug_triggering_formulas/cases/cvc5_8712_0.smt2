(declare-const a Real)
(declare-const b Int)
(assert (> a (/ (to_real b) (to_real 0))))
(check-sat)
