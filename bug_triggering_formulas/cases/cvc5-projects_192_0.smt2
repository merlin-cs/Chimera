(declare-fun g () a)
(declare-fun e (a a) a)
(assert (forall ((f a) (h a)) (= (e f h) (ite ((_ is d) f) h (ite ((_ is b) f) (b (e (c f) h)) g)))))
(check-sat)
