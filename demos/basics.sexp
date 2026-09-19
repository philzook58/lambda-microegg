;██╗      █████╗ ███╗   ███╗██████╗ ██████╗  █████╗     ███████╗ ██████╗  ██████╗ 
;██║     ██╔══██╗████╗ ████║██╔══██╗██╔══██╗██╔══██╗    ██╔════╝██╔════╝ ██╔════╝ 
;██║     ███████║██╔████╔██║██████╔╝██║  ██║███████║    █████╗  ██║  ███╗██║  ███╗
;██║     ██╔══██║██║╚██╔╝██║██╔══██╗██║  ██║██╔══██║    ██╔══╝  ██║   ██║██║   ██║
;███████╗██║  ██║██║ ╚═╝ ██║██████╔╝██████╔╝██║  ██║    ███████╗╚██████╔╝╚██████╔╝
;╚══════╝╚═╝  ╚═╝╚═╝     ╚═╝╚═════╝ ╚═════╝ ╚═╝  ╚═╝    ╚══════╝ ╚═════╝  ╚═════╝ 
                                                                                 
                                                                                                                            

(echo "Lambda MicroEgg is an e-graph equality-saturation engine with support for binders such as lambda, sum, integrate, etc.")

(echo "It can still do basic rewriting")

(insert (/ (* a 2) 2))
(rewrite (* ?x 2) (<< ?x 2))
(rewrite (/ (* ?x ?y) ?y) ?x)
(run 10)
(extract (/ (* a 2) 2))
(print-egraph)

(reset)


(union (double a) (* a 2)) ; you can also manually union stuff
(guard (double a) (* a 2)) ; Test they are equal.

(reset)

(echo "------------------------------------------------------------")

(echo "Some special forms are useful for higher-order rewriting.")
(echo "Square brackets allow patterns in function position.")
(echo "They automatically curry into binary application nodes.")
(echo "Spiritually, though not literally, `[f x y]` is `(app (app f x) y)`.")

(insert [f x y])
; This matches with ?g = f.
(match [?g x y])
; This does not match because [] and () denote distinct node types.
(match (f x y))

(echo "------------------------------------------------------------")
(echo "More interesting is support for bound variables.")

(echo "@ marks an operator as a binder, represented distinctly from application nodes.")
(insert
  (@sum x
    (@sum y
      (+ x y))))

(echo "A metavariable can contain bound variables listed in its allowed occurrences.")
(echo "This is a Miller higher-order pattern.")

; There are two matches, one for each sum. The second, corresponding to
; `(@sum y (+ x y))`, contains a free variable.
(match (@sum x {?a x}))

; This fails because the body contains x but ?a is not marked as allowing x.
(match (@sum x ?a))

(rewrite
  (@sum x (+ {?a x} {?b x}))
  (+ (@sum x {?a x})
     (@sum x {?b x})))

(run 3)

(guard
   (@sum x
    (@sum y
      (+ x y)))

   (+ (@sum x (@sum y x))
      (@sum x (@sum y y)))
)


