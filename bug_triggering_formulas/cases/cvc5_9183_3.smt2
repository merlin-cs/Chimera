(declare-const a Real)
(declare-const b Real)
(assert (> 1.0 (/ (/ b a) (/ 0.0 b))))
(check-sat)
