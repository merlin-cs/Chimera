(declare-fun a () Int)
(assert (forall ((b Int)) (> (ite (or (> 1 b) (> b (div 1 a))) a 1) (div 1 a))))
(assert (not (= a 0)))
(check-sat)
