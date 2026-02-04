(declare-const a (Array (_ BitVec 64) (_ BitVec 64)))
(declare-const b (_ BitVec 64))
(assert (= (store a (select a b) (bvor b b)) (store (store a b b) (select a #x0000000000000000) (bvadd #x1111111111111111 b))))
(check-sat)
