theorem random_uf_3 {α : Type} (x0 x1 x2 : α) (h0 : x2 = x0) : x0 = x2 := by
  let e0 := x0
  let e2 := x2
  let p0 : x0 = e0 := rfl
  let p2 : x2 = e2 := rfl
  -- random union 0: x2 = x0
  let p3 : e2 = e0 := h0
  let p5 : e0 = e2 := Eq.symm p3
  let p6 : e2 = x2 := Eq.symm p2
  let p7 : e0 = x2 := Eq.trans p5 p6
  let p8 : x0 = x2 := Eq.trans p0 p7
  exact p8
