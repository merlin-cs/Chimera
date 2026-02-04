(declare-fun x (Real) Real)
(assert (ite false false (forall ((_x Real)) (= (* _x _x) (+ 0.0 (x real.pi))))))
(check-sat)
