(declare-fun a () (Set Real))
(assert (= (union a (singleton 0)) (intersection a (singleton 0))))
(check-sat)
