(define-sort FPN () Float64)

(declare-fun y () FPN)
(assert (= (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp.min y (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(check-sat)
