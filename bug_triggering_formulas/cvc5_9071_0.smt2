(declare-fun x ((_ BitVec 1)) (_ BitVec 1))
(assert (exists ((y (_ BitVec 1))) (= (x y) (_ bv0 1))))
(check-sat)
