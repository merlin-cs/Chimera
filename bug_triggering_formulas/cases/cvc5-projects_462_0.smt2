(declare-const _x3 Int)
(assert (>= (str.to_code (str.from_code _x3)) _x3))
(check-sat)
