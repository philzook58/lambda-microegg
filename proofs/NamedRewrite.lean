theorem two_rewrites {α : Type} (plus : α → α → α) (zero x : α) (r1 : ∀ a, plus a zero = a) : plus (plus x zero) zero = x := by
  let e0 := x
  let e1 := zero
  let e2 := plus
  let e3 := e2 e0
  let e4 := e3 e1
  let e5 := e2 e4
  let e6 := e5 e1
  let p7 : e4 = e0 := r1 e0
  let p8 : e5 = e3 := congrArg e2 p7
  let p9 : e6 = e4 := congrFun p8 e1
  let p10 : e6 = e0 := Eq.trans p9 p7
  exact p10
