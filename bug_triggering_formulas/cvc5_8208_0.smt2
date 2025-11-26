(declare-const a Real)
(declare-const b Real)
(assert (< (sin a) (/ 0.0 (sin b))))
(check-sat)
