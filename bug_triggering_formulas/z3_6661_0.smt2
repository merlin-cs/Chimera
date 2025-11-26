(declare-sort U 0)

(declare-fun R (U U) Bool)
(assert (forall ((x U) (y U)) (= (R x y) ((_ transitive-closure 0) x y))))
(declare-fun a () U)
(assert (not (R a a)))
(check-sat)
