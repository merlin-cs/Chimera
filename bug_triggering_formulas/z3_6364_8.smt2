(declare-fun a (Int) Int)
(declare-fun b (Int Int Real) (Array Int (Array Int Real)))
(assert (forall ((c Int) (d Real)) (or (< 0 c) (= d (select (select (b (a 0) (a c) d) 0) 0)))))
(check-sat)
