(assert (forall ((a Int) (b Int)) (=> (<= a 0) (= a (ite (= b 0) a (div a b))))))
(check-sat)
