(declare-const x (d RegLan RegLan))
(declare-const _x t)
(assert (str.in_re (_s _x) (re.++ re.all (s x))))
(check-sat)
