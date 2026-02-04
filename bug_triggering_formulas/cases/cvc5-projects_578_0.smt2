(declare-const x d)
(assert (= ((_ is _c) x) ((_ is c) ((_ update _s) x true))))
(check-sat)
