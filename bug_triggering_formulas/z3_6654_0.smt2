(declare-sort A 0)

(declare-sort A 0)

(declare-const a A)
(assert (not (R a a)))
(check-sat)
(declare-const x A)
(declare-const y A)
(declare-const z A)
(assert (not (forall ((x A) (y A) (z A)) (=> (and (R x y) (R x z)) (or (R y z) (R z y))))))
(check-sat)
