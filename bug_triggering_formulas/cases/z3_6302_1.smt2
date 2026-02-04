(assert (forall ((v Int)) (or (= 0 (mod v 2)) (= 0 (div v 2)))))
(check-sat)
