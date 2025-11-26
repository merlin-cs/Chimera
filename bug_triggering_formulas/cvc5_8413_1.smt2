(declare-fun a () (_ BitVec 1))
(assert (= (_ bv0 1) (bvand (_ bv1 1) (bvneg (bvlshr a (_ bv0 1))))))
(check-sat)
