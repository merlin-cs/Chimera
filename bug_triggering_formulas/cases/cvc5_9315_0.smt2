(declare-fun v () Real)
(assert (exists ((V Real)) (= v (- (* 1.0 (set.choose (set.insert (to_real (to_int (arcsin v))) (arcsin 0.0) v (set.singleton 1.0))))))))
(check-sat)
