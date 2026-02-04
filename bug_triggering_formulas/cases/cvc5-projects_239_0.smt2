(declare-fun a () Real)
(declare-fun b () Real)
(assert (> (* (* (/ 3 a) a) 84 b) 1))
(check-sat)
