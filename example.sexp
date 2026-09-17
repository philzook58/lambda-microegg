; Variables beginning with ? are rewrite metavariables.
; Lambda-bound variables are named. $0 is reserved for an outer context.
; Bare ?x cannot capture a binder; (?x x) explicitly permits binder x.
(insert (lam x (+ (f x) 0)))
(match (lam x (?body x)))
(rewrite (+ ?x 0) ?x)
(rewrite (f ?x) ?x)
(run 10)
(extract (lam x (+ (f x) 0)))
