(declare-sort Loc 0)

(declare-const x1 Loc)
(declare-const x2 Loc)
(assert (pto x1 x2))
(assert (not (pto x2 x2)))
(check-sat)
