(assert (not (forall ((x Real) (d Real)) (exists ((y Real)) (= (+ (* 3 x) d) (+ y (to_int y) (to_int (- y))))))))
(check-sat)
