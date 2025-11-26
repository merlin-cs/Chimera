(declare-fun p (Int) Int)
(assert (forall ((x Int)) (> (ite (= 0 (p 1)) 0 (mod x (p 1))) (mod 2 (p 0)))))
(check-sat)
