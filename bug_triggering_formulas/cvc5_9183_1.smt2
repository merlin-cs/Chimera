(declare-fun r () Real)
(assert (forall ((v Real)) (< (/ (* r r) v 0.0) 0.0)))
(check-sat)
