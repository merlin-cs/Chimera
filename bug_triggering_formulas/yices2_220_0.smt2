(declare-const _30-0 (_ BitVec 30))
(assert (= (bvadd (bvmul (concat (_ bv64 7) (bvneg _30-0)) (concat (_ bv64 7) (bvneg _30-0))) (bvadd (concat (_ bv64 7) (bvneg _30-0)) (bvmul (concat (_ bv64 7) (bvneg _30-0)) (concat (_ bv64 7) (bvneg _30-0))))) (bvadd (concat (_ bv64 7) (bvneg _30-0)) (bvmul (concat (_ bv64 7) (bvneg _30-0)) (concat (_ bv64 7) (bvneg _30-0)))) (concat (_ bv64 7) (bvneg _30-0))))
(check-sat)
