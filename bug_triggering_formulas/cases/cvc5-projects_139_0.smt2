(declare-sort S4 0)

(declare-fun _substvar_25_ () (_ BitVec 13))
(assert (forall ((q15 S4) (q16 (_ BitVec 20)) (q17 (_ BitVec 13))) (= _substvar_25_ (bvudiv (_ bv0 13) (_ bv0 13)) q17 (bvsrem (_ bv0 13) (_ bv0 13)) q17)))
(check-sat)
