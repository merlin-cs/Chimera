(declare-fun a () Int)
(declare-fun b () Int)
(assert (> (/ 0.5 (cos 0.5) (/ b (/ (+ 0.5 (ite (= a 0) 0 1)) 0))) 0))
(check-sat)
