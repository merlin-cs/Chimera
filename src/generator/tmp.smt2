(declare-fun r9g () Real)
(declare-fun 1q3t () Real)
(declare-fun 1jy () Real)

(assert (not (and (or (< 1q3t 51.483507) (> 23 real.pi)) (and (< 85 real.pi) (> 77 1jy)))))
(check-sat)
(exit)