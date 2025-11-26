(declare-fun a () Int)
(assert (forall ((b Int)) (= (mod (+ (mod b 4) a) 4) 2)))
(check-sat)
