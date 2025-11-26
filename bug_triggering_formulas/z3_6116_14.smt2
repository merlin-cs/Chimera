(assert (or true (= (bv2nat ((_ int2bv 3) (bv2nat ((_ int2bv 1) 1)))) (bv2nat ((_ int2bv 1) (bv2nat ((_ int2bv 1) (bv2nat ((_ int2bv 3) 0)))))))))
(check-sat)
