(declare-fun x () l)
(declare-fun y () t)
(assert (distinct y (c x)))
(check-sat)
