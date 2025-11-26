(declare-fun b (Int) Bool)
(declare-fun v () Int)
(assert (= (b 0) (= "B" (str.++ "B" (str.substr "A" 0 v)))))
(check-sat)
