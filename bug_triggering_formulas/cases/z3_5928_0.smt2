(declare-fun v () String)
(assert (forall ((a String)) (exists ((v String)) (not (str.in_re (str.++ a (str.from_int 0)) (re.inter (str.to_re a) (str.to_re v)))))))
(assert (= 0 (str.to.int v)))
(check-sat)
