(declare-const i7 Int)
(assert (xor true true true true true (<= (mod 0 (mod i7 5)) 46) true true true true))
(assert (< 775 (mod 0 0)))
(check-sat)
