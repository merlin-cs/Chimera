(declare-sort s 0)

(declare-sort t 0)

(declare-fun d (s t) t)
(declare-fun f () t)
(declare-fun m (s t) a)
(declare-fun n (t) Int)
(declare-fun j () Bool)
(assert (forall ((e s)) (distinct b (m e f))))
(assert (forall ((i s) (g s) (h t)) (= (m i (d i h)) (ite (= i g) b c))))
(assert (forall ((h t)) (= (= h f) (distinct 0 (n h)))))
(assert (exists ((i s) (h t)) (distinct (n (d i h)) (ite j 0 (n h)))))
(check-sat)
