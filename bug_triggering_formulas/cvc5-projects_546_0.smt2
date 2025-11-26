(declare-const x String)
(assert (str.is_digit (str.rev x)))
(check-sat)
