(echo "Beta reduction through a Miller pattern")

(insert (app (lam x (pair x x)) z))
(rewrite
  (app (lam x (?body x)) ?arg)
  (#subst (?body x) x ?arg))
(run 10)
(extract (app (lam x (pair x x)) z))
