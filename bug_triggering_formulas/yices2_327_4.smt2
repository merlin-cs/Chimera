(declare-const x Bool)
(declare-const y Bool)
(assert (xor x y true (forall ((z Int)) (= z 0))))
(check-sat)
