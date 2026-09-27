theorem first_order_congruence {α : Type} (f : α → α) (a b : α) (h0 : a = b) : f a = f b := by
  let e0 := f
  let e1 := a
  let e2 := b
  let e3 := e0 e1
  let e4 := e0 e2
  -- input equality a = b
  let p10 : e1 = e2 := h0
  let p12 : e2 = e1 := Eq.symm p10
  let p13 : e4 = e3 := congrArg e0 p12
  let p16 : e3 = e4 := Eq.symm p13
  exact p16
