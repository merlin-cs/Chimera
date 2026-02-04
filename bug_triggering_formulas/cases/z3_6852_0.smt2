(declare-fun v () Bool)
(assert (forall ((f Bool)) (<= (+ (ite f 1 0) (ite v 1 0)) 1)))
(check-sat)
