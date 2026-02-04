(declare-fun a () Bool)
(assert (forall ((b Int)) (or a (= b 0))))
(assert (= (rem 0 0) 1))
(check-sat)
