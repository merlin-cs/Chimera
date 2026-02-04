(declare-const a (_ BitVec 26))
(check-sat)
(assert (not (= (_ bv0 1) (bvand (bvnot (bvsub (_ bv1 1) (bvudiv (_ bv0 1) (bvnot ((_ extract 25 25) a))))) (bvcomp (_ bv0 17) ((_ zero_extend 6) ((_ extract 25 15) a)))))))
(check-sat)
