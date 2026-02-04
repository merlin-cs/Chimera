(declare-const x (_ BitVec 1))
(assert (bvsgt x (_ bv0 1)))
(check-sat)
