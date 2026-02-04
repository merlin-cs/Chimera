(declare-fun e () Real)
(assert (not (xor (= 0.0 0.0) (= e 0) (= e e) (= e 0) (= e e))))
(check-sat)
