(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re (str.++ (ite (str.in_re b (re.* (re.range "a" "u"))) (str.substr a 0 0) "B") b) (re.++ (re.range "a" "u") (re.diff (re.* re.allchar) (str.to_re "")))))
(check-sat)
