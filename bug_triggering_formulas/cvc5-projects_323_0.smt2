(declare-const x Real)
(declare-const x1 Real)
(assert (let ((_let1 (exists ((x2 String)) (= (= x x1) (distinct "" x2))))) (not (ite _let1 _let1 (= x x1)))))
(check-sat)
