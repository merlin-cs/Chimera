(declare-const b Int)
(assert (= (* b b) (+ b 1)))
(check-sat)
