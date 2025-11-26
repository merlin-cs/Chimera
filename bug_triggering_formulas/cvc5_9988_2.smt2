(declare-fun a () String)
(declare-fun b () String)
(assert (not (str.in_re (str.++ b "z" a) (re.++ (re.* (str.to_re "z")) (str.to_re (str.replace_re (str.++ b "b" b) (re.++ (re.union (re.* (re.range "a" "z")) (str.to_re (str.replace "z" a ""))) (re.++ (re.opt (str.to_re "z")) (str.to_re "b"))) ""))))))
(check-sat)
