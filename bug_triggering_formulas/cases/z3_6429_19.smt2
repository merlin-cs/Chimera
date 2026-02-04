(declare-fun a () Int)
(declare-fun b () (Array Int (Array Int Int)))
(assert (or (exists ((c Int)) (> c (- a))) (exists ((d Int) (e Int)) (distinct (= 1 (select (select b d) 0)) (distinct (< e 1) (>= d 0 e))))))
(check-sat)
