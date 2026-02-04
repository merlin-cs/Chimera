(declare-fun _substvar_238_ () Bool)
(declare-fun _substvar_280_ () Bool)
(assert (xor true true _substvar_238_ _substvar_280_ (exists ((q9 (_ BitVec 8)) (q10 (_ BitVec 8)) (q11 (_ BitVec 6))) (bvult (_ bv0 6) q11)) true true))
(check-sat)
