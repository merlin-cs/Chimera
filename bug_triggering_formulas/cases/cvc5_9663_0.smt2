(declare-fun a () String)
(assert (str.in_re a (re.diff (re.range "" "") (re.range "" "A"))))
(check-sat)
