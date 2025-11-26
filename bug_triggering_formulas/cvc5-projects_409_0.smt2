(assert (str.in_re (str.from_code 0) ((_ re.loop 2 1) re.all)))
(check-sat)
