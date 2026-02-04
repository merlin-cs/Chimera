(declare-sort S)

(declare-fun f (S S) S)
(declare-fun g () S)
(assert (forall ((e S)) (not (= e (f g e)))))
(assert (forall ((u S) (v S)) (= (f u v) (f v v))))
(check-sat)
