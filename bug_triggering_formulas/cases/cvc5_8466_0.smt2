(declare-fun a (Bool) Bool)
(assert (forall ((b Bool)) (= (a b) (not b))))
(check-sat)
