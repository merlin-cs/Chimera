(define-sort a () (_ FloatingPoint 8 4))

(declare-fun b () a)
(assert (distinct (forall ((c a)) (distinct (fp.abs c) b))))
(check-sat)
