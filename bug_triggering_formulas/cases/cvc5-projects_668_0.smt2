(declare-sort u 0)

(declare-const x u)
(assert (seq.nth (seq.unit (set.is_singleton (set.minus (set.singleton (_ bv0 67)) (set.singleton (_ bv0 67))))) (set.card (set.singleton x))))
(check-sat)
