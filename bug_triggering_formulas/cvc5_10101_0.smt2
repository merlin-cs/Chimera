(declare-const l (Seq String))
(assert (not (str.prefixof "abc" l)))
(check-sat)
