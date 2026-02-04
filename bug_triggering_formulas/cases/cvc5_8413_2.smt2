(declare-fun a () (_ BitVec 1))
(assert (forall ((b (_ BitVec 1))) (not (bvugt (bvneg b) a))))
(check-sat)
