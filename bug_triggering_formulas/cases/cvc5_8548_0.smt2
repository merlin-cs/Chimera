(declare-const a String)
(declare-const b String)
(assert (str.in_re b (re.++ (re.opt re.allchar) (re.diff (re.* re.none) (str.to_re b)))))
(check-sat)
