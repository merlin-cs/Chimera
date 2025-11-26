(declare-sort D)

(declare-fun f (MyOption D) D)
(assert (not (= (f (Some (elem 1))) (f (Some (elem 2))))))
(check-sat)
