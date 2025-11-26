(declare-sort C 0)

(declare-sort h 0)

(declare-sort r 0)

(declare-fun p () Bool)
(declare-fun s () r)
(declare-fun e (a) C)
(declare-fun u (h a) Bool)
(declare-fun u (C C) Bool)
(declare-fun u (h C) C)
(declare-fun u (r C) h)
(assert (forall ((q C) (v2 h)) (= (and (forall ((v a)) p) (forall ((v a)) (not (u v2 v)))) (forall ((v a)) (or (not (u v2 v)) (u (e n) (u (u s q) q)))))))
(check-sat)
