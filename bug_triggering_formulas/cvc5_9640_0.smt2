(declare-const x Bool)
(declare-fun e () Real)
(assert (forall ((q Real)) (= x (< q e))))
(check-sat)
