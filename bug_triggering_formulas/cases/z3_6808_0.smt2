(declare-const x Bool)
(assert (distinct (_ bv0 32) (ite (distinct (_ bv0 32) (ite x (_ bv1 32) (_ bv0 32))) (_ bv1 32) (_ bv0 32))))
(check-sat)
