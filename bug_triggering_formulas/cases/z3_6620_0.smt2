(declare-const a (_ BitVec 64))
(assert (distinct (bvlshr a a) (bvurem a a)))
(check-sat)
