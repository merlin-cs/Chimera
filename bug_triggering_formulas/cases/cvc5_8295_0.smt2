(declare-fun str9 () String)
(assert (str.in_re str9 (re.* (re.union re.allchar (str.to_re "lE")))))
(check-sat)
