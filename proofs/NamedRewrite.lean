theorem two_rewrites {α : Type} (app : α → α → α) (plus zero x : α) (r1 : ∀ a, app (app plus a) zero = a) : app (app (plus) (app (app (plus) (x)) (zero))) (zero) = x := by
  let e0 := x
  let e1 := zero
  let e2 := plus
  let e3 := app e2 e0
  let e4 := app e3 e1
  let e5 := app e2 e4
  let e6 := app e5 e1
  let p7 : e4 = e0 := by simpa only [] using r1 e0
  let p8 : e5 = e3 := congrArg (app e2) p7
  let p9 : e6 = e4 := congrFun (congrArg app p8) e1
  let p10 : e6 = e0 := Eq.trans p9 p7
  exact p10
