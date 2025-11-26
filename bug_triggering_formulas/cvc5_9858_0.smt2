(define-sort S16 () Float64)

(define-sort S37 () (Array S16 Int))

(declare-const c S37)
(assert (= 0 (select c (fp.min (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp (_ bv1 1) (_ bv0 11) (_ bv0 52))))))
(check-sat)
