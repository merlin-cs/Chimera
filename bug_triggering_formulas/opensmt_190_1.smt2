(declare-sort S2 0)

(declare-sort S3 0)

(declare-sort S4 0)

(declare-sort S2 0)

(declare-sort S2 0)

(declare-sort S3 0)

(declare-sort S4 0)

(declare-sort S2 0)

(declare-fun uf4 (Bool Bool Bool Bool) Bool)
(declare-fun uf7 (Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun v3 () Bool)
(declare-fun v8 () Bool)
(declare-fun v11 () Bool)
(declare-fun v17 () Bool)
(check-sat)
(check-sat)
(assert (uf7 (=> v3 v11) true true true true v8 true))
(push)
(assert (= v3 v17))
(push)
(assert false)
(check-sat)
(pop)
(check-sat)
(check-sat)
(pop)
(push)
(assert (uf4 (= (=> v3 v11) (not v8)) true true true))
(check-sat)
(check-sat)
(pop)
(assert (=> v3 v11))
(check-sat)
