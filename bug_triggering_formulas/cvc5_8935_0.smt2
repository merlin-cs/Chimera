(declare-fun a () String)
(assert (ite (= (- 1) (str.to_int a)) false true))
(check-sat)
