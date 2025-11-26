(declare-fun b (Real) Real)
(declare-fun v () Real)
(assert (and (distinct 0 (* v v)) (= 0.0 (b (exp 1.0)))))
(check-sat)
