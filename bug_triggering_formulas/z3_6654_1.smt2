(declare-sort A 0)

(declare-const x A)
(declare-const y A)
(declare-const z A)
(assert (not (forall ((x A) (y A) (z A)) (=> (and (R y x) (R z x)) (or (R y z) (R z y))))))
(check-sat)
