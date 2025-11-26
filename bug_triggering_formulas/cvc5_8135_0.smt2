(declare-const a Int)
(declare-const b Int)
(assert (> (- a) (* (+ a a) (+ a 1))))
(check-sat)
