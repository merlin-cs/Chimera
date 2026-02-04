(declare-fun v () Int)
(assert (exists ((e Int)) (forall ((E Int)) (= 0 e))))
(assert (distinct 0 (+ 1 (div v (* v v)))))
(check-sat)
