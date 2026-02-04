(declare-const arr1 (Array Bool Bool))
(assert (not (exists ((q1 (_ BitVec 10)) (q2 (Array Bool Bool)) (q3 Bool) (q4 (Array Bool Bool))) (not (= q4 q2 q2 q4 q2)))))
(assert (select arr1 true))
(check-sat)
