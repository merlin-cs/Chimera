(declare-const a Real)
(declare-const b Real)
(assert (> b (to_real (mod 0 a))))
(check-sat)
