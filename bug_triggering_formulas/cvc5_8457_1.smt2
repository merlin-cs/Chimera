(declare-fun b (Int Int) Bool)
(assert (forall ((a Int) (v String)) (or (b a 0) (distinct 0 (str.indexof v (str.substr v 1 1) 0)))))
(check-sat)
