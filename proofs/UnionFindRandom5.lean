theorem random_uf_5 {α : Type} (x0 x1 x2 x3 x4 : α) (h3 : x0 = x4) : x0 = x4 := by
  let e0 := x0
  let e4 := x4
  let p0 : x0 = e0 := rfl
  let p4 : x4 = e4 := rfl
  -- random union 3: x0 = x4
  let p8 : e0 = e4 := h3
  let p9 : e4 = x4 := Eq.symm p4
  let p10 : e0 = x4 := Eq.trans p8 p9
  let p11 : x0 = x4 := Eq.trans p0 p10
  exact p11
