(declare-const v (_ BitVec 1))
(assert (forall ((V (_ BitVec 1))) (= (_ bv0 28943) (bvadd ((_ zero_extend 28942) v) ((_ zero_extend 28942) v)))))
(check-sat)
