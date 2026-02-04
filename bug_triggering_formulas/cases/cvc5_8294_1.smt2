(declare-fun r3 () Real)
(assert (= 0.0 (+ (- r3) (cos r3) (- 1.0))))
(check-sat)
