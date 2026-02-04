(declare-sort u 0)

(declare-sort _u 0)

(declare-const x (Array _u u))
(assert (distinct x x))
(check-sat)
