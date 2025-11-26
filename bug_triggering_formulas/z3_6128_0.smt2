(assert (forall ((v (Array Real Real)) (a Int) (V Real)) (distinct v (store (store (store v 0.0 1.0) 1.0 (to_real a)) 0.0 0.0))))
(check-sat)
