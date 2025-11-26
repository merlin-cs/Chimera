(declare-fun a () (_ BitVec 16))
(assert (not (= (_ bv1 32) ((_ zero_extend 16) a))))
(assert (bvsgt ((_ zero_extend 16) a) (_ bv1 32)))
(check-sat)
