(declare-fun m (Int Int) Bool)
(declare-fun x () Int)
(assert (forall ((e Int)) (distinct (xor (m e 0)) (= 1 (+ x (* e (- 2)))))))
(check-sat)
