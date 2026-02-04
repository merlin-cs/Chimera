(declare-sort a 0)

(declare-sort b 0)

(declare-sort c 0)

(declare-sort d 0)

(declare-sort o 0)

(declare-sort s 0)

(declare-fun e () (-> a (-> d Bool)))
(declare-fun f () (-> a (-> d Bool)))
(declare-fun g ((-> a (-> d Bool)) b (-> a (-> d Bool))) s)
(declare-fun h (o s) Bool)
(declare-fun p () c)
(declare-fun q () o)
(declare-fun u (c) b)
(declare-fun v (b d o d) Bool)
(assert (not (h q (g e (u p) f))))
(assert (forall ((i o) (j (-> a (-> d Bool))) (k b) (l (-> a (-> d Bool)))) (= (h i (g j k l)) (forall ((m a) (n d)) (= (j m n) (forall ((r d)) (= (v k n i r) (l m r))))))))
(check-sat)
