(declare-const _x3 String)
(declare-const _x5 Real)
(assert (let ((_let0 (bv2nat #b000000000000000000000000000000000001))) (let ((_let1 (str.rev _x3))) (= _let1 (str.at (str.update _let1 _let0 _let1) _let0)))))
(check-sat)
