(declare-sort a 0)

(declare-fun i (t l) l)
(assert (forall ((u t)) (forall ((t l)) (distinct N (i u N)))))
(check-sat)
