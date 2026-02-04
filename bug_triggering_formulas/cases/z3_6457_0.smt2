(declare-const a Float32)
(declare-const b Float32)
(assert (fp.isNaN (fp.sub roundNearestTiesToEven (fp (_ bv0 1) (_ bv255 8) (_ bv0 23)) (fp.add roundNearestTiesToEven a b))))
(check-sat)
