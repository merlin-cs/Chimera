(declare-fun a ((Array Int (Array Int Real))) (Array Int (Array Int Real)))
(declare-fun a ((Array Int (Array Int Real)) (Array Int (Array Int Real))) (Array Int (Array Int Real)))
(assert (forall ((b Int) (c Int) (d (Array Int (Array Int Real))) (e (Array Int (Array Int Real)))) (or (= (select (e b) 1) 0) (distinct (select (select (a d d) b) 1) (select (select (a e (a d)) c) 0)))))
(check-sat)
