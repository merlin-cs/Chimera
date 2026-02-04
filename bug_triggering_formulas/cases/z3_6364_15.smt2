(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 1))
(assert (forall ((c (_ BitVec 2))) (= (_ bv0 3) (bvadd (bvneg ((_ zero_extend 1) c)) (concat (_ bv0 1) ((_ extract 0 0) (bvlshr ((_ zero_extend 14) a) (concat (_ bv0 13) (_ bv0 1) (_ bv0 1) (bvnand (_ bv1 1) (bvand b ((_ extract 0 0) c)))))) (_ bv0 1))))))
(check-sat)
