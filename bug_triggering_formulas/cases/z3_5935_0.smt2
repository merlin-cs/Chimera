(declare-fun r () String)
(declare-fun v () String)
(assert (forall ((a String)) (or (= v (str.++ a r "t")) (= (str.at (str.substr a 0 1) 1) (str.at (str.substr v 0 (str.len a)) 2)))))
(check-sat)
