(declare-fun a () Float32)
(assert (forall ((b Float32)) (not (fp.isPositive (fp.max a b)))))
(check-sat)
