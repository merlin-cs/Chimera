(declare-fun a () String)
(assert (str.prefixof (str.substr a 0 10) 2))
(check-sat)
