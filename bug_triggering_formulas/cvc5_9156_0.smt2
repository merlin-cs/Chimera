(declare-fun a () String)
(assert (= (str.len a) 0))
(assert (str.contains (str.substr a 0 (- 1 0)) "G"))
(check-sat)
