(assert (= ((_ to_fp 5 11) roundTowardZero (_ bv0 11)) (fp (_ bv0 1) (_ bv0 5) (_ bv0 10))))
(check-sat)
