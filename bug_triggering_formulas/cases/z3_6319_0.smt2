(declare-fun p (Int) Int)
(assert (= (p 0) 1))
(assert (forall ((i Int)) (or (<= i 0) (= (p i) (* 2 (p (- i 1)))))))
(check-sat)
