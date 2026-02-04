(define-sort FPN () Float64)

(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(assert (distinct r (fp.min x y)))
(check-sat)
