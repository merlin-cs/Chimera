(declare-sort S 0)

(declare-fun a (S S) Int)
(declare-fun b () S)
(declare-fun c (S S) S)
(declare-fun d () S)
(assert (forall ((e S)) (< 1 (a b (c e (c d e))))))
(assert (forall ((e S) (f S) (g S)) (>= (a b (c d (c b e))) (a b (c g (c b b))))))
(check-sat)
