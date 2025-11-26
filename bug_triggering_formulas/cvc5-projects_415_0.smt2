(declare-sort _u0 0)

(declare-sort _u56 0)

(define-sort _s0 (_y0) _u0)

(declare-const _x108 (Bag (_ BitVec 100)))
(declare-const _x112 (Bag _u56))
(declare-fun _x113 ((_ BitVec 100)) _u0)
(assert (bag.subbag (bag _x112 (bag.card (bag.map _x113 _x108))) (bag _x112 (bag.card _x108))))
(check-sat)
