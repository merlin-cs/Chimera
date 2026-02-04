(assert (exists ((v String)) (= "" (str.replace_re v re.allchar v))))
(check-sat)
