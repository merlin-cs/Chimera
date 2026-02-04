(declare-fun ol_7 () Bool)
(assert (or (not (or false (and ol_7 false false false false) false))))
(check-sat)
