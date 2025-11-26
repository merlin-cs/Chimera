(declare-const a Real)
(declare-const b Real)
(assert (> (/ (/ b b) (/ b b)) (/ b (/ b b))))
(check-sat)
