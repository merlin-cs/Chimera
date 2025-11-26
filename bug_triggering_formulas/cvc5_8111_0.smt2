(declare-fun v () String)
(assert (forall ((V String)) (str.in_re (str.++ "" v) (re.++ (str.to_re "b") (re.union (str.to_re "") (str.to_re "z"))))))
(check-sat)
