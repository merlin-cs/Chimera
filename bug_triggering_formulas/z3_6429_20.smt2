(declare-fun a () Real)
(assert (or true (or (or (not (distinct 0 a)) (not (= a 0))))))
(check-sat)
