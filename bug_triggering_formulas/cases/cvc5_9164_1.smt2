(declare-const a Real)
(declare-const b Real)
(assert (> (/ 1.0 (/ a b)) (/ (* a a) a)))
(check-sat)
