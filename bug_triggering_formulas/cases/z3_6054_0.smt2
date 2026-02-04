(declare-fun v () Int)
(declare-fun a () Int)
(assert (distinct true (= "" (str.replace (str.substr "A" 0 a) "" (str.substr "A" 0 v)))))
(check-sat)
