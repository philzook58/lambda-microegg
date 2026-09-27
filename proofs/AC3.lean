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
  let e12 := e8 e2
  let e13 := e4 e12
  let e14 := e3 e9
  let e15 := e14 e2
  let e16 := e4 e2
  let e17 := e8 e16
  let e18 := e10 e1
  let e19 := e3 e18
  let e20 := e19 e0
  let e22 := e10 e0
  let e23 := e8 e22
  let e24 := e3 e22
  let e25 := e24 e1
  let t18 := e3 e1
  let t19 := t18 e0
  let t20 := e8 e0
  let t21 := e3 t19
  let t22 := e3 e9
  let t23 := e3 e5
  let t24 := t21 e2
  let t25 := e6 e2
  let t26 := e3 e0
  let t27 := t26 e2
  let t28 := e4 e2
  let t29 := t18 t27
  let t30 := e8 e16
  let t37 := t18 e2
  let t38 := e8 e2
  let t39 := e3 t37
  let t40 := e3 e18
  let t41 := t39 e0
  let t42 := e19 e0
  let t43 := e3 e2
  let t44 := t43 e0
  let t45 := e10 e0
  let t46 := t18 t44
  let t47 := e8 e22
  let t48 := t43 e1
  let t49 := e10 e1
  let t50 := e3 t48
  let t51 := t50 e0
  let t52 := t43 t19
  let t53 := e10 e9
  let t56 := t18 e16
  let t57 := e3 e16
  let t58 := e3 e22
  let t59 := t57 e1
  let t60 := e24 e1
  let p14 : e7 = e13 := assoc e0 e1 e2
  let p15 : e5 = e9 := comm e0 e1
  let p18 : e11 = e15 := comm e2 e9
  let p19 : e9 = e5 := Eq.symm p15
  let p20 : e14 = e6 := congrArg e3 p19
  let p21 : e15 = e7 := congrFun p20 e2
  let p22 : e15 = e13 := Eq.trans p21 p14
  let p23 : e11 = e13 := Eq.trans p18 p22
  let p27 : e8 = t18 := rfl
  let p28 : t18 = e8 := Eq.symm p27
  let p29 : t19 = t20 := congrFun p28 e0
  let p30 : e9 = t20 := rfl
  let p32 : t20 = e9 := Eq.symm p30
  let p33 : t19 = e9 := Eq.trans p29 p32
  let p34 : t21 = t22 := congrArg e3 p33
  let p35 : e6 = t23 := rfl
  let p36 : t23 = t22 := congrArg e3 p15
  let p37 : e6 = t22 := Eq.trans p35 p36
  let p38 : t22 = e6 := Eq.symm p37
  let p39 : t21 = e6 := Eq.trans p34 p38
  let p40 : t24 = t25 := congrFun p39 e2
  let p41 : e7 = t25 := rfl
  let p43 : t25 = e7 := Eq.symm p41
  let p44 : t24 = e7 := Eq.trans p40 p43
  let p45 : t24 = e13 := Eq.trans p44 p14
  let p47 : e4 = t26 := rfl
  let p48 : t26 = e4 := Eq.symm p47
  let p49 : t27 = t28 := congrFun p48 e2
  let p50 : e16 = t28 := rfl
  let p52 : t28 = e16 := Eq.symm p50
  let p53 : t27 = e16 := Eq.trans p49 p52
  let p54 : t29 = t30 := congr p28 p53
  let p55 : e17 = t30 := rfl
  let p57 : t30 = e17 := Eq.symm p55
  let p58 : t29 = e17 := Eq.trans p54 p57
  let p59 : t24 = t29 := assoc e1 e0 e2
  let p60 : e13 = t24 := Eq.symm p45
  let p61 : e13 = t29 := Eq.trans p60 p59
  let p62 : e13 = e17 := Eq.trans p61 p58
  let p64 : e12 = e18 := comm e1 e2
  let p65 : e11 = e17 := Eq.trans p23 p62
  let p66 : e7 = e17 := Eq.trans p14 p62
  let p75 : t37 = t38 := congrFun p28 e2
  let p76 : e12 = t38 := rfl
  let p78 : t38 = e12 := Eq.symm p76
  let p79 : t37 = e12 := Eq.trans p75 p78
  let p80 : t37 = e18 := Eq.trans p79 p64
  let p81 : t39 = t40 := congrArg e3 p80
  let p82 : e19 = t40 := rfl
  let p84 : t40 = e19 := Eq.symm p82
  let p85 : t39 = e19 := Eq.trans p81 p84
  let p86 : t41 = t42 := congrFun p85 e0
  let p87 : e20 = t42 := rfl
  let p89 : t42 = e20 := Eq.symm p87
  let p90 : t41 = e20 := Eq.trans p86 p89
  let p92 : e10 = t43 := rfl
  let p93 : t43 = e10 := Eq.symm p92
  let p94 : t44 = t45 := congrFun p93 e0
  let p95 : e22 = t45 := rfl
  let p97 : t45 = e22 := Eq.symm p95
  let p98 : t44 = e22 := Eq.trans p94 p97
  let p99 : t46 = t47 := congr p28 p98
  let p100 : e23 = t47 := rfl
  let p102 : t47 = e23 := Eq.symm p100
  let p103 : t46 = e23 := Eq.trans p99 p102
  let p104 : t41 = t46 := assoc e1 e2 e0
  let p105 : e20 = t41 := Eq.symm p90
  let p106 : e20 = t46 := Eq.trans p105 p104
  let p107 : e20 = e23 := Eq.trans p106 p103
  let p108 : t48 = t49 := congrFun p93 e1
  let p109 : e18 = t49 := rfl
  let p111 : t49 = e18 := Eq.symm p109
  let p112 : t48 = e18 := Eq.trans p108 p111
  let p113 : t50 = t40 := congrArg e3 p112
  let p114 : t50 = e19 := Eq.trans p113 p84
  let p115 : t51 = t42 := congrFun p114 e0
  let p116 : t51 = e20 := Eq.trans p115 p89
  let p117 : t51 = e23 := Eq.trans p116 p107
  let p118 : t52 = t53 := congr p93 p33
  let p119 : e11 = t53 := rfl
  let p121 : t53 = e11 := Eq.symm p119
  let p122 : t52 = e11 := Eq.trans p118 p121
  let p123 : t52 = e17 := Eq.trans p122 p65
  let p124 : t51 = t52 := assoc e2 e1 e0
  let p125 : e23 = t51 := Eq.symm p117
  let p126 : e20 = t51 := Eq.trans p107 p125
  let p127 : e20 = t52 := Eq.trans p126 p124
  let p128 : e20 = e17 := Eq.trans p127 p123
  let p129 : e23 = e20 := Eq.symm p107
  let p130 : e23 = e17 := Eq.trans p129 p128
  let p131 : e16 = e22 := comm e0 e2
  let p135 : t56 = t47 := congr p28 p131
  let p136 : t56 = e23 := Eq.trans p135 p102
  let p137 : t56 = e17 := Eq.trans p136 p130
  let p138 : t57 = t58 := congrArg e3 p131
  let p139 : e24 = t58 := rfl
  let p141 : t58 = e24 := Eq.symm p139
  let p142 : t57 = e24 := Eq.trans p138 p141
  let p143 : t59 = t60 := congrFun p142 e1
  let p144 : e25 = t60 := rfl
  let p146 : t60 = e25 := Eq.symm p144
  let p147 : t59 = e25 := Eq.trans p143 p146
  let p148 : t56 = t59 := comm e1 e16
  let p149 : e17 = t56 := Eq.symm p137
  let p150 : e17 = t59 := Eq.trans p149 p148
  let p151 : e17 = e25 := Eq.trans p150 p147
  let p153 : e7 = e25 := Eq.trans p66 p151
  let p154 : e11 = e25 := Eq.trans p65 p151
  let p159 : e25 = e11 := Eq.symm p154
  let p160 : e7 = e11 := Eq.trans p153 p159
  exact p160
