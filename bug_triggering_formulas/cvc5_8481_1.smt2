(declare-fun v () String)
(assert (str.in_re (str.++ v v) (re.++ (str.to_re "a") (re.opt (str.to_re "a")))))
(assert (str.in_re v (re.range "a" "u")))
(check-sat)
