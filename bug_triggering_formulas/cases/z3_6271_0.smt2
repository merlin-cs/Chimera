(assert (forall ((v Real)) (distinct 1 (mod (to_int v) 3))))
(check-sat)
