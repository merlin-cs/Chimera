(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (= x y (= x false)))
(check-sat)
