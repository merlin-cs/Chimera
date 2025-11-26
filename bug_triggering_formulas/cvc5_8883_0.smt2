(declare-fun p2 () (Data Bool))
(declare-fun p3 () (Data Bool))
(assert (not (= p2 p3)))
(check-sat)
