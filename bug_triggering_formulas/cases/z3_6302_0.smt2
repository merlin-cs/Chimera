(assert (forall ((v Int)) (or (= 0 (div v 1)) (distinct 0 (mod v 2)))))
(check-sat)
