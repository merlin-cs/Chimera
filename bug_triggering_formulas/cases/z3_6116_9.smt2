(declare-fun a () Int)
(assert (= ((_ int2bv 1) a) (_ bv0 1)))
(check-sat)
