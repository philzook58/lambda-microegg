; Summation manipulation rules.
; https://en.wikipedia.org/wiki/Summation#Identities
; https://courses.cs.washington.edu/courses/cse373/19sp/resources/math/summation/

(echo "Linearity and moving an index-independent factor outside a sum")

(insert
  (@sum i
    (+ (* c (a i))
       (* d (b i)))))

; Sum distributes over addition and subtraction.
(rewrite
  (@sum i (+ {?f i} {?g i}))
  (+ (@sum i {?f i})
     (@sum i {?g i})))
(rewrite
  (@sum i (- {?f i} {?g i}))
  (- (@sum i {?f i})
     (@sum i {?g i})))

; A bare ?c cannot capture i, which supplies the usual side condition
; that c is independent of the summation index.
(rewrite
  (@sum i (* ?c {?f i}))
  (* ?c (@sum i {?f i})))
(rewrite
  (@sum i (* {?f i} ?c))
  (* ?c (@sum i {?f i})))

(run 10)
(guard
  (@sum i (+ (* c (a i)) (* d (b i))))
  (+ (* c (@sum i (a i)))
     (* d (@sum i (b i)))))
(extract
  (@sum i (+ (* c (a i)) (* d (b i)))))

(reset)
(echo "A constant sum is the constant times the number of terms")

; Keeping the number of terms as (sum_i 1) makes this valid for an
; otherwise unspecified summation range.
(insert (@sum i c))
(rewrite
  (@sum i ?c)
  (* ?c (@sum i 1)))
(run 5)
(guard (@sum i c) (* c (@sum i 1)))
(extract (@sum i c))

(reset)
(echo "Two sums over the same range may exchange their dummy indices")

(insert (@sum i (@sum j (a i j))))

; The LHS Miller arguments stay in context order. The RHS application
; performs the permutation explicitly.
(rewrite
  (@sum i (@sum j {?f i j}))
  (@sum i (@sum j {?f j i})))

(run 5)
(guard
  (@sum i (@sum j (a i j)))
  (@sum i (@sum j (a j i))))
(extract (@sum i (@sum j (a i j))))

(reset)
(echo "Closed forms for sums from 1 through n")

; Here the range is explicit: (sum-1-to n (@lam i body)).
(insert
  (+ (sum-1-to n (@lam i i))
     (sum-1-to n (@lam i (^ i 2)))))

(rewrite
  (sum-1-to ?n (@lam i i))
  (/ (* ?n (+ ?n 1)) 2))
(rewrite
  (sum-1-to ?n (@lam i (^ i 2)))
  (/ (* ?n (* (+ ?n 1) (+ (* 2 ?n) 1))) 6))
(rewrite
  (sum-1-to ?n (@lam i ?c))
  (* ?n ?c))

(run 10)
(guard
  (+ (sum-1-to n (@lam i i))
     (sum-1-to n (@lam i (^ i 2))))
  (+ (/ (* n (+ n 1)) 2)
     (/ (* n (* (+ n 1) (+ (* 2 n) 1))) 6)))
(extract
  (+ (sum-1-to n (@lam i i))
     (sum-1-to n (@lam i (^ i 2)))))
