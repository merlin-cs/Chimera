(declare-fun a () (_ BitVec 32))
(assert (forall ((b (_ BitVec 32)) (c (_ BitVec 32))) (=> (= c (bvand (bvadd b (_ bv1 32)) (_ bv31 32))) (bvslt (bvmul ((_ sign_extend 32) a) ((_ sign_extend 32) c)) (bvsdiv ((_ sign_extend 32) a) ((_ sign_extend 32) b))))))
(check-sat)
