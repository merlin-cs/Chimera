(declare-const x (_ BitVec 1))
(assert (= (_ bv0 1) (bvashr (_ bv1 1) (bvcomp (_ bv0 2) ((_ zero_extend 1) x)))))
(check-sat)
