(declare-const x Int)
(declare-fun v () String)
(assert (= "0" (str.substr v 0 x)))
(check-sat)
