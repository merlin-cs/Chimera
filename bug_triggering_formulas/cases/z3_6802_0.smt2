(declare-const n Int)
(declare-const m Int)
(assert (= (+ (+ (^ 0 0) 4) 4) m n))
(check-sat)
