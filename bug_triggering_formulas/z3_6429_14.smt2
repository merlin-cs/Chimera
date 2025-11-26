(declare-fun D () Float32)
(assert (= (_ bv0 1) (ite (fp.gt (fp.add roundTowardPositive D (_ +zero 8 24)) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))) (_ bv1 1) (_ bv0 1))))
(check-sat)
