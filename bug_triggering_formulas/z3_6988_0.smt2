(declare-fun r () Real)
(assert (= 0.0 (/ 1.0 1.0 r)))
(check-sat)
