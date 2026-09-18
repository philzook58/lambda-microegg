; Haskell-style rewrite rules.
; Inspired by GHC RULES and HLint:
; https://downloads.haskell.org/~ghc/7.0.1/docs/html/users_guide/rewrite-rules.html
; https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml

(echo "Map fusion builds a lambda and beta-reduces its body")

(insert
  (map
    (lam x (+ x 1))
    (map (lam y (* y 2)) xs)))

; map f (map g xs) = map (f . g) xs
; Writing composition as a lambda exercises capture-avoiding substitution.
(rewrite
  (map ?f (map ?g ?xs))
  (map (lam z (app ?f (app ?g z))) ?xs))

; beta
(rewrite
  (app (lam x (?body x)) ?arg)
  (#subst (?body x) x ?arg))

; Two small HLint-style list simplifications.
(rewrite (map (lam x x) ?xs) ?xs)
(rewrite (concat (map ?f ?xs)) (concat-map ?f ?xs))

(run 10)
(extract
  (map
    (lam x (+ x 1))
    (map (lam y (* y 2)) xs)))
(guard
  (map
    (lam x (+ x 1))
    (map (lam y (* y 2)) xs))
  (map (lam z (+ (* z 2) 1)) xs))

(echo "Map identity and concat-map fire in the same ruleset")
(insert (concat (map (lam x x) ys)))
(run 10)
(extract (concat (map (lam x x) ys)))
(guard (concat (map (lam x x) ys)) (concat-map (lam x x) ys))

(reset)
(echo "Short-cut deforestation: foldr consumes build without making a list")

; foldr k z (build g) = g k z
(rewrite
  (foldr ?k ?z (build ?g))
  (app (app ?g ?k) ?z))
(rewrite
  (app (lam x (?body x)) ?arg)
  (#subst (?body x) x ?arg))

; A producer for [a,b], abstracted over cons and nil.
(insert
  (foldr cons nil
    (build
      (lam c
        (lam n
          (app (app c a)
            (app (app c b) n)))))))

(run 10)
(extract
  (foldr cons nil
    (build
      (lam c
        (lam n
          (app (app c a)
            (app (app c b) n)))))))
(guard
  (foldr cons nil
    (build
      (lam c
        (lam n
          (app (app c a)
            (app (app c b) n))))))
  (app (app cons a) (app (app cons b) nil)))
