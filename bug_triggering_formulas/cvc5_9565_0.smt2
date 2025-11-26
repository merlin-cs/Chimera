(declare-fun e () Real)
(assert (= (* e e) (+ 1.0 1.0)))
(check-sat)
