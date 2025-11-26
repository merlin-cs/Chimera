(assert (forall ((a Int) (b Int)) (distinct 0 (+ (ite (= a b) a (div a (* a a))) 1))))
(check-sat)
