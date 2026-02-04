(assert (set.subset (set.complement (set.singleton (_ -oo 5 11))) (set.singleton (fp.abs (set.choose (set.complement (set.singleton (_ -oo 5 11))))))))
(check-sat)
