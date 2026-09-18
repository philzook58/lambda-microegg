(insert (f a))
(union a b)
(extract a)
(extract (f a))
(extract (f b))
(guard (f a) (f b))
;(guard (f a) (f c))
(insert (f c))
(insert 1 (f $0))
(insert 2 (f $1)) ; doesn't make a new term
(insert 4 (f $2)) ; nor does this

(match (f ?a)) ; 3 matches. a, c and $0


(reset)
; We need to explictly announce which variables are allowed in 
; TODO: Should I lambda wrap ?a ?
(insert 0 (lam x x))
(match (lam x ?a)) ; no matches. 
(match (lam x (?a x))) ; match ctx 0: a = $0

(reset)
; ok, de bruijn levels. But then shifting something outside a lambda to the top may require shifting?
(insert 0 (lam x (lam y x))) ; de buijn level
(match (lam z (?a z)))  ; de bruijn indices
; but the pattern then is confusing. What is $0 referring to? If we don't know the context we're in
; We can't know that $0 refers to the visible lambda.

;(match 0 (lam z (?a $0))) ; non ambgiuos

(match (lam z ?a)) ; 

(reset)

; the two inner lambdas should be seen as equal
(insert 0 (+ (lam x (lam y y)) (lam z z)))
(match (+ (lam w ?a) ?a)) 

(reset)

(union 1 (* $0 0) 0)
(match (* ?a 0))

; Maybe nice to be able to dump internal full lift form
; Useful to generalize lam(body) to lam(dump, body) ? Mark out which vars of body are captured.
; generalizes both levels and indices
; lam/bind is a useful if we rarely bind, we don't want app f to always allow for binding.
; We weaken more than bind

(reset)

(insert 0 (#subst $0 $0 fred))
(match fred)
(print-egraph)

;
(reset)
(echo "subst carries equalities?")
(union 1 (* $0 0) (* 0 $0))
(print-egraph)
(insert 0 (#subst (* $0 0) $0 42))
;(print-egraph) ; yup looks good.
(guard (* 42 0) (* 0 42))


; negative guards
; multipatterns and pattern guards (* 42 ?a) (* ?a 42)
; Subst should carry temporary lambda that's different from interned lambda?
;subst has special case if we're substituting in correctly ordered variable?
; should just be a thinning.
; If we supported swap, it'd be likewise.


; meet is pullback
; join is coproduct
; if we flip cod/dom of thin. Probably better to have pullback that pushout?

; has this been worth it?

(reset)
(insert 0 (lam x x))
(match (lam x (?a x)))


(reset)
(insert 0 (lam y (lam x x)))
(match (lam x (lam y (?a x y))))
(match (lam x (lam y (?a x y))))


(reset)
(insert 0 (lam y (lam x y)))
(match (lam x (lam y (?a x y))))
(match (lam x (lam y (?a x y))))
(print-egraph)



(reset)
; twisted miller is rejected
;(match (lam x (lam y (pair (?a x y) (?a y x)))))

(insert 0 (sum (lam x (sum (lam y (sum (lam z (a x y z))))))))
(rewrite
  (sum (lam x (sum (lam y (?m x y)))))
  (sum (lam x (sum (lam y (?m y x))))))

  
(reset)

(insert 0 (lam x x))
(rewrite  (lam x (?a x)) (?a (foo biz)))
(run 1)
(print-egraph)


(reset)
;(insert 0 (lam z (lam x (lam y (y z))))