(declare-fun v () String)
(declare-fun r () Bool)
(assert (forall ((V String)) (or r (exists ((V String)) (str.in_re (str.++ "z" v) (re.* (str.to_re (str.from_code (str.len v)))))))))
(check-sat)
