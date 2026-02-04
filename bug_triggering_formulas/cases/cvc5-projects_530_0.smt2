(declare-const x Real)
(assert (= real.pi (/ real.pi (tan (to_real (to_int x))))))
(assert (= 1 (to_int x)))
(check-sat)
