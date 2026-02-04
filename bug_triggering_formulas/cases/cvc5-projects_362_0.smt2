(declare-sort A$ 0)

(declare-sort Real_set$ 0)

(declare-sort Real_a_fun$ 0)

(declare-sort Real_filter$ 0)

(declare-fun z$ () Real)
(declare-fun g1$ () Real_a_fun$)
(declare-fun g2$ (Real) A$)
(declare-fun uu$ () Real_a_fun$)
(declare-fun top$ () Real_set$)
(declare-fun scaleR$ (Real A$) A$)
(declare-fun fun_app$ (Real_a_fun$ Real) A$)
(declare-fun at_within$ (Real Real_set$) Real_filter$)
(declare-fun atLeastAtMost$ (Real Real) Real_set$)
(declare-fun vector_derivative$ (Real_a_fun$ Real_filter$) A$)
(assert (forall ((?v0 Real)) (= (fun_app$ uu$ ?v0) (ite (<= (* ?v0 2.0) 1.0) (fun_app$ g1$ (* 2.0 ?v0)) (g2$ (- (* 2.0 ?v0) 1.0))))))
(assert (not (= (vector_derivative$ uu$ (at_within$ z$ (atLeastAtMost$ 0.0 1.0))) (scaleR$ 2.0 (vector_derivative$ g1$ (at_within$ (* z$ 2.0) (atLeastAtMost$ 0.0 1.0)))))))
(assert (= (vector_derivative$ uu$ (at_within$ z$ (atLeastAtMost$ 0.0 1.0))) (scaleR$ 2.0 (vector_derivative$ g1$ (at_within$ (* z$ 2.0) top$)))))
(assert (= (vector_derivative$ g1$ (at_within$ (* z$ 2.0) (atLeastAtMost$ 0.0 1.0))) (vector_derivative$ g1$ (at_within$ (* z$ 2.0) top$))))
(check-sat)
