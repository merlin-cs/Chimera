(declare-fun a () Int)
(declare-fun b () Int)
(assert (= 0 (* b (/ a (- 1)))))
(check-sat)
