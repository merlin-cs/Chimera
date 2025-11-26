(declare-fun t ((Array Int (Array Int Real))) (Array Int (Array Int Real)))
(declare-fun p ((Array Int (Array Int Real)) (Array Int (Array Int Real))) (Array Int (Array Int Real)))
(assert (forall ((a (Array Int (Array Int Real))) (b (Array Int (Array Int Real)))) (distinct (select (p b (p b (t b))) 1) (select (p a (p b (p (t b) (t b)))) 0))))
(check-sat)
