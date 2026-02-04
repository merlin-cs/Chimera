(declare-sort a 0)

(assert (forall ((x a) (y a)) (= x y)))
(check-sat)
