(declare-sort u 0)

(declare-const x u)
(assert (forall ((_x u)) (= _x x)))
(check-sat)
