(declare-fun v () Int)
(declare-fun a () Int)
(assert (= "" (str.replace (str.substr "A" 0 v) "" (str.substr "A" 0 a))))
(check-sat)
