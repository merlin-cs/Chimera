(declare-fun v () String)
(assert (str.in_re (str.++ v "b" v) (re.++ (str.to_re "aa") (re.* (str.to_re "b")))))
(check-sat)
