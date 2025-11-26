(assert (set.choose (set.insert (set.is_singleton (set.complement (set.singleton true))) (set.complement (set.complement (set.singleton true))))))
(check-sat)
