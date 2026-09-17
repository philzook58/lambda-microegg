(echo "Basic rewriting")

(insert (+ (* a 1) 0))
(rewrite (+ ?x 0) ?x)
(rewrite (* ?x 1) ?x)
(run 10)
(extract (+ (* a 1) 0))
(print-egraph)
