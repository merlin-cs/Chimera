(declare-fun v () (_ BitVec 2))
(assert (= v (ite (= (_ bv1 1) ((_ extract 1 1) v)) (_ bv0 2) (bvneg v))))
(check-sat)
