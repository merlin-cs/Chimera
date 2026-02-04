(declare-fun a () String)
(assert (str.in_re a (re.++ (re.+ (str.to_re "AB")) (str.to_re "B"))))
(check-sat)
