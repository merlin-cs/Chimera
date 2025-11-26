(declare-sort a 0)

(declare-sort ao 0)

(declare-sort b 0)

(declare-fun c (b a) ao)
(declare-fun aa () b)
(declare-fun f (ao) a)
(declare-fun ab (ao Int) a)
(declare-fun acc (ao ao) a)
(declare-fun ad (ao ao Int) Bool)
(assert (forall ((?j b) (?k b) (?l a)) (exists ((?m a)) (forall ((?n Int)) (= (ad (c ?j ?l) (c ?k ?m) ?n) (forall ((?ae a)) (forall ((?q Int)) (= (< ?q ?n) (distinct (f (c ?k (acc (c ?j ?ae) (c ?k ?m)))) (f (c ?k (acc (c ?j ?l) (c ?j (ab (c ?j ?ae) ?q))))))))))))))
(assert (forall ((?t a)) (forall ((?ai a)) (forall ((?aj a)) (exists ((?ak a)) (not (= (distinct ?ak (acc (c aa ?aj) (c aa ?ai))) (forall ((?u a)) (= ?u (ab (c aa ?t) 1))))))))))
(check-sat)
