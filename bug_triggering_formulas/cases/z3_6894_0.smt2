(declare-const x Bool)
(declare-fun z () (_ BitVec 1))
(assert (= (_ bv1 1) ((_ extract 0 0) (ite (bvsle (ite (and (= z (_ bv1 1)) (= (_ bv1 1) (ite x (_ bv0 1) (bvshl (_ bv1 1) z)))) (_ bv1 1) (_ bv0 1)) (_ bv1 1)) (_ bv1 2) ((_ zero_extend 1) (ite x (_ bv0 1) (bvshl (_ bv1 1) z)))))))
(check-sat)
