(declare-fun b (Int) Bool)
(assert (exists ((r String)) (distinct (- 1) (str.to_int (str.substr r 1 1)))))
(assert (forall ((v Int)) (exists ((a Int)) (not (b (+ 1 v))))))
(check-sat)
