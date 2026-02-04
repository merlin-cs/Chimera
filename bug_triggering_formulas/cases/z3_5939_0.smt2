(declare-fun a () Int)
(assert (exists ((v Int)) (= a (mod v (- 3)))))
(check-sat)
