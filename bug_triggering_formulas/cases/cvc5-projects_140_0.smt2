(declare-fun a () Int)
(declare-fun b (Int Int) Bool)
(assert (forall ((c Int) (d Int)) (xor (> a d 0) (b c d))))
(check-sat)
