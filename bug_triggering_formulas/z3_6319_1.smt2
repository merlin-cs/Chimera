(declare-fun o (Int) Int)
(assert (and (= 1 (o 0)) (forall ((i Int)) (or (not (> i 0)) (= (o i) (* 2 (o (- i 1))))))))
(check-sat)
