(declare-fun x (Bool Bool) Bool)
(assert (forall ((x4 Bool)) (x x4 (x false false))))
(check-sat)
