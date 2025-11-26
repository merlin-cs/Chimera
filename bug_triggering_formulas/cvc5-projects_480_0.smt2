(declare-const x Real)
(assert (= x (- (* 1.0 (set.choose (set.insert (to_real (to_int (arcsin x))) (arcsin 0.0) x (set.singleton 1.0)))))))
(assert ((_ divisible 3) (set.choose (set.complement (set.singleton (to_int (arcsin x)))))))
(check-sat)
