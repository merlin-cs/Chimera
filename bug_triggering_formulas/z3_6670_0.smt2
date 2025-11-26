(declare-fun i () Int)
(assert (> (rem i i) 0))
(check-sat)
