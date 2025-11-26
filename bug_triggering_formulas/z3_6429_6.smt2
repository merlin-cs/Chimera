(assert (forall ((a Int) (b Int) (c Int) (d Int)) (not (= (mod (+ (- a b (mod c 2)) d) 3) 0))))
(check-sat)
