(assert (or (exists ((v Real)) (= 0.0 (* 1.0 (set.choose (set.insert (to_real (to_int (arcsin v))) v (set.singleton 1.0)))))) (forall ((v Real)) (= 0.0 (* v v)))))
(check-sat)
