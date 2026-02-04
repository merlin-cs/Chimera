(declare-fun a () Int)
(assert (not (ite (= a 0) true false)))
(check-sat)
