(echo "A Miller variable explicitly admits the local x binder")

(insert 1 (@lam x (pair $0 x)))
(match (@lam x (pair ?outer {?body x})))

(echo "Without the x argument, ?body cannot capture x")
(match (@lam x (pair ?outer ?body)))

(reset)
(echo "RHS Miller application can permute its temporarily named parameters")
(insert (@lam x (@lam y (pair x y))))
(rewrite
  (@lam x (@lam y {?a x y}))
  (@lam x (@lam y {?a y x})))
(run 4)
(guard
  (@lam x (@lam y (pair x y)))
  (@lam x (@lam y (pair y x))))
