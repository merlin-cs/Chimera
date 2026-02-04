(declare-fun h (Int) Int)
(assert (= f h))
(assert (= 0 (h 0)))
(check-sat)
