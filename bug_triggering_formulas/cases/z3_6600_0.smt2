(declare-fun v () String)
(assert (= 0 (seq.last_indexof "H" v)))
(check-sat)
