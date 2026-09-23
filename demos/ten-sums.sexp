; Stress nested binder permutation and linearity with ten summation indices.

(insert
  (@sum x0
    (@sum x1
      (@sum x2
        (@sum x3
          (@sum x4
            (@sum x5
              (@sum x6
                (@sum x7
                  (@sum x8
                    (@sum x9 (+ x0 x1))))))))))))

; Adjacent sums commute. The RHS reverses the binders while passing the
; variables back to the body in their original semantic order.
(rewrite
  (@sum x (@sum y {?a x y}))
  (@sum y (@sum x {?a x y})))

; Summation is linear over addition.
(rewrite
  (@sum x (+ {?a x} {?b x}))
  (+ (@sum x {?a x}) (@sum x {?b x})))

; Addition is commutative.
(rewrite (+ ?a ?b) (+ ?b ?a))

(run 10)

; The two outermost sums can exchange order without capturing either index.
(guard
  (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x0 x1)))))))))))
  (@sum x1 (@sum x0 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x0 x1))))))))))))

; Addition may commute inside all ten binders.
(guard
  (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x0 x1)))))))))))
  (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x1 x0))))))))))))

; Repeated linearity moves the addition outside every summation.
(guard
  (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x0 x1)))))))))))
  (+
    (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 x0))))))))))
    (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 x1))))))))))))

(extract
  (@sum x0 (@sum x1 (@sum x2 (@sum x3 (@sum x4 (@sum x5 (@sum x6 (@sum x7 (@sum x8 (@sum x9 (+ x0 x1))))))))))))
