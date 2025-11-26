(assert (exists ((x Int)) (and (< 0 x) (> 0 (div 1 (* 2 x))))))
(check-sat)
