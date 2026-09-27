theorem ac3 {α : Type} (plus : α → α → α) (x0 x1 x2 : α) (assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)) (comm : ∀ a b, plus a b = plus b a) : plus (plus x0 x1) x2 = plus x2 (plus x1 x0) := by
  let e0 := x0
  let e1 := x1
  let e2 := x2
  let e3 := plus
  let e4 := e3 e0
  let e5 := e4 e1
  let e6 := e3 e5
  let e7 := e6 e2
  let e8 := e3 e1
  let e9 := e8 e0
  let e10 := e3 e2
  let e11 := e10 e9
  let e14 := e3 e9
  let e15 := e14 e2
  let p1 : e5 = e9 := comm e0 e1
  let p2 : e11 = e15 := comm e2 e9
  let p106 : e9 = e5 := Eq.symm p1
  let p107 : e14 = e6 := congrArg e3 p106
  let p108 : e15 = e7 := congrFun p107 e2
  let p140 : e7 = e15 := Eq.symm p108
  let p141 : e15 = e11 := Eq.symm p2
  let p142 : e7 = e11 := Eq.trans p140 p141
  exact p142
