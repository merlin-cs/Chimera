(declare-sort S 0)

(declare-fun a () S)
(declare-fun f (S S) S)
(declare-fun g (S S) S)
(assert (= (f a a) (f a (f a (f a a)))))
(assert (forall ((x S) (y S)) (= (f (f a a) a) (ite (= (f (f a x) a) a) a (ite (= (f (f a y) a) a) a (f a (f (g a x) y)))))))
(assert (forall ((x S) (y S)) (= (f a (f a y)) (f a (f (f a x) y)))))
(check-sat)
