(declare-fun e () Int)
(declare-fun v () Int)
(assert (and (= 0 (bv2nat ((_ int2bv 2) e))) (= (+ e 1) (bv2nat ((_ int2bv 2) v)))))
(check-sat)
