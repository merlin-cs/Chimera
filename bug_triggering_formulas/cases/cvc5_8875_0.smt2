(declare-fun a () (MyList Int))
(assert (> (hd a) 50))
(assert (not (and ((_ is cons) a) (not ((_ is nelem) a)))))
(check-sat)
