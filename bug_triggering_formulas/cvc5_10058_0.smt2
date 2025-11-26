(assert (distinct (exists ((V Int)) false) (exists ((v String)) (distinct true (str.< (str.replace_all v v "") (str.replace (str.++ v "fi") "fi" (str.rev "fi")))))))
(check-sat)
