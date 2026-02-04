(declare-fun TRUE () Int)
(declare-fun FALSE () Int)
(assert (not (<= (* (- FALSE (- (* TRUE TRUE))) FALSE) (- (+ (mod (abs FALSE) (+ (int.pow2 TRUE) (abs FALSE))) (int.pow2 (abs (int.pow2 FALSE))))))))
(check-sat)
