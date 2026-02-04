(declare-fun v () Real)
(assert (< 0.0 (* v (mod (to_int v) (to_int (* 1.0 (to_int (/ v v))))))))
(check-sat)
