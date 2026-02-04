(declare-const _36-1 (_ BitVec 36))
(assert (bvugt (bvsrem (_ bv0 67) (bvsdiv (concat (_ bv0 31) _36-1) (concat (_ bv0 31) _36-1))) (_ bv0 67)))
(check-sat)
