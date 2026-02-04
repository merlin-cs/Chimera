(declare-fun a () Int)
(assert (exists ((b Int)) (and (<= 2 a) (= (mod b (+ a a)) (+ b 7)))))
(check-sat)
