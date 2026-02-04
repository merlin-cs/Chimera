(assert (bvuge (_ bv0 32) (bvand (_ bv0 32) (bvmul (bvxnor (_ bv0 32) (_ bv0 32)) ((_ zero_extend 24) (_ bv30 8))))))
(check-sat)
