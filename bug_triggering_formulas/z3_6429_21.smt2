(assert (= 0 (ite (or false) 1 0)))
(check-sat)
