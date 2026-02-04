(declare-const a Int)
(assert (forall ((b Real)) (exists ((c Real)) (<= (+ a b (* a c)) 0))))
(check-sat)
