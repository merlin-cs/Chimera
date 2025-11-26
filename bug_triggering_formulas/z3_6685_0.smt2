(declare-fun l1 () mylist)
(declare-fun l2 () mylist)
(assert (exists ((x Int)) (and (= (head l1) x) (not (= (head l2) x)))))
(check-sat)
