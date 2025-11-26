(declare-fun v () String)
(declare-fun m () Int)
(assert (< 0 (- (- (seq.last_indexof "JH" v)) m)))
(check-sat)
