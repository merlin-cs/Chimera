(declare-fun a () String)
(assert (str.in_re (str.replace_re a (str.to_re "") a) (re.++ re.allchar (str.to_re "A"))))
(check-sat)
