(assert false)
(assert (xor false (not (not (not false)))))
(check-sat)
