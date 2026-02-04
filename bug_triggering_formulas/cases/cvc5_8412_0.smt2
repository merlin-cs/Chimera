(declare-fun x () (_ BitVec 2))
(assert (distinct true (bvule (bvsdiv (_ bv0 2) x) (_ bv0 2))))
(check-sat)
