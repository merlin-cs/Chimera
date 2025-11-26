(declare-fun v () String)
(assert (str.in_re (str.++ v v) (re.++ (str.to_re "b") (re.* (str.to_re v)))))
(assert (str.in_re (str.++ v v) (re.++ (re.* (str.to_re "c")) (str.to_re "a"))))
(check-sat)
