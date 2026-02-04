(declare-fun a () Real)
(assert (forall ((b Real)) (and (= b 0.0) (not (is_int a)))))
(check-sat)
