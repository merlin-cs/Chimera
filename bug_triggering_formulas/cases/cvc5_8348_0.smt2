(declare-fun x () (Bag Int))
(declare-fun t () (Bag Int))
(assert (distinct false (exists ((E Int)) (= 1 (+ (bag.card x) (bag.card (bag.difference_subtract x t)))))))
(check-sat)
