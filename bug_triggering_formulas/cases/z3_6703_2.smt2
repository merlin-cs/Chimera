(declare-fun e () Int)
(declare-fun i () Int)
(assert (= (* i 2) (- (+ e 2 (mod (- e 1) e)))))
(check-sat)
