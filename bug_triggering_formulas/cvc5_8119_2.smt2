(declare-fun a (Int) Int)
(assert (exists ((b Int)) (and (> b 0) (distinct (ite (= 0 (a b)) (a 1) (mod 0 (a b))) (ite (= 0 (a b)) (a 1) (mod (- (a 1) (ite (= 0 (a 1)) 0 (mod 0 (a 1)))) (a b)))))))
(check-sat)
