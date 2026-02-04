(declare-fun a () Int)
(declare-fun b () Real)
(assert (forall ((c Real)) (or (= a c) (= b (+ (* b b) 1.0)))))
(check-sat)
