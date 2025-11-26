(declare-const x (_ BitVec 3))
(assert (bvule (bvnand s s) s))
(check-sat)
