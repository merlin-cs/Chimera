(assert (exists ((v Int)) (forall ((a Int)) (= 0 (mod (+ v a) 2)))))
(check-sat)
