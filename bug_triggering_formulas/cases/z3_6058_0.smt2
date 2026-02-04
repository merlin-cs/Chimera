(declare-const x Bool)
(declare-fun v () Int)
(assert (or true x (and false (= (_ bv0 14) ((_ int2bv 14) v)) (= (_ bv0 14) (bvurem (_ bv1 14) ((_ int2bv 14) 1))))))
(check-sat)
