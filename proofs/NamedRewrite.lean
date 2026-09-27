theorem two_rewrites {α : Type} (app : α → α → α) (plus zero x : α) (r1 : ∀ a, app (app plus a) zero = a) : app (app (plus) (app (app (plus) (x)) (zero))) (zero) = x := by
  let e0 := x
  let e1 := zero
  let e2 := plus
  let e3 := app e2 e0
  let e4 := app e3 e1
  let e5 := app e2 e4
  let e6 := app e5 e1
  let t7 := app e2 e0
  let t8 := app t7 e1
  let t9 := app e3 e1
  let p8 : e3 = t7 := rfl
  let p9 : t7 = e3 := Eq.symm p8
  let p10 : t8 = t9 := congrFun (congrArg app p9) e1
  let p11 : e4 = t9 := rfl
  let p13 : t9 = e4 := Eq.symm p11
  let p14 : t8 = e4 := Eq.trans p10 p13
  let p15 : t8 = e0 := r1 e0
  let p16 : e4 = t8 := Eq.symm p14
  let p17 : e4 = e0 := Eq.trans p16 p15
  let p18 : e5 = e3 := congrArg (app e2) p17
  let p19 : e6 = e4 := congrFun (congrArg app p18) e1
  let p20 : e6 = e0 := Eq.trans p19 p17
  exact p20
