theorem random_uf_4 {α : Type} (x0 x1 x2 x3 : α) (h1 : x0 = x2) (h2 : x2 = x3) : x0 = x3 := by
  let e0 := x0
  let e2 := x2
  let e3 := x3
  let p0 : x0 = e0 := rfl
  let p3 : x3 = e3 := rfl
  -- random union 1: x0 = x2
  let p5 : e0 = e2 := h1
  -- random union 2: x2 = x3
  let p6 : e2 = e3 := h2
  let p7 : e0 = e3 := Eq.trans p5 p6
  let p8 : e3 = x3 := Eq.symm p3
  let p9 : e0 = x3 := Eq.trans p7 p8
  let p10 : x0 = x3 := Eq.trans p0 p9
  exact p10
