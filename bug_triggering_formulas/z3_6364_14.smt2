(declare-fun p (Int) Int)
(assert (forall ((i Int)) (or (> i 0) (= (p i) (- 1 (p (- i)))))))
(check-sat)
