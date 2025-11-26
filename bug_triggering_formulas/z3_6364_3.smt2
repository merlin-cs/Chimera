(declare-fun f (Real Real) Real)
(declare-fun g (Real Real) (Array Real Real))
(assert (forall ((a Real) (b Real) (c Real) (d Real)) (=> (<= b a c) (= (select (g (f b c) d) a) d))))
(check-sat)
