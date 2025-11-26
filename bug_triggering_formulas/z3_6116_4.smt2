(declare-const a Int)
(assert (> (- a) (mod 1 (- 1))))
(check-sat)
