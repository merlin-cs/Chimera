(declare-const s String)
(declare-const r RegLan)
(assert (str.prefixof s r))
(check-sat)
