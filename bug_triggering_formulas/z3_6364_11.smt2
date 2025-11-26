(declare-fun a (Int) Bool)
(assert (forall ((b Int)) (a b)))
(check-sat)
