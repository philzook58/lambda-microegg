(echo "Beta reduction through a Miller pattern")

(insert [(@lam x (pair x x)) z])

; The beta rule. It isn't quite a built in, since @ and {} are generic binder constructs.
; But it is pretty close to being built in.
(rewrite
  [(@lam x {?body x}) ?arg]
  {?body ?arg})

(run 10)

(extract [(@lam x (pair x x)) z])
(guard [(@lam x (pair x x)) z] (pair z z))
