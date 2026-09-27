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
  let t14 := e3 e0
  let t15 := t14 e1
  let t16 := e4 e1
  let t17 := e3 t15
  let t18 := e3 e5
  let t19 := t17 e2
  let t20 := e6 e2
  let t21 := e3 e1
  let t22 := t21 e2
  let t23 := e8 e2
  let t24 := t14 t22
  let t25 := e4 e12
  let t26 := t21 e0
  let t27 := e8 e0
  let t30 := e3 e2
  let t31 := t30 e9
  let t32 := e10 e9
  let t33 := e3 e9
  let t34 := t33 e2
  let t35 := e14 e2
  let t38 := e3 t26
  let t39 := t38 e2
  let t40 := t14 e2
  let t41 := e4 e2
  let t42 := t21 t40
  let t43 := e8 e16
  let t45 := t30 e1
  let t46 := e10 e1
  let t52 := e3 t22
  let t53 := e3 e18
  let t54 := t52 e0
  let t55 := e19 e0
  let t56 := t30 e0
  let t57 := e10 e0
  let t58 := t21 t56
  let t59 := e8 e22
  let t60 := e3 t45
  let t61 := t60 e0
  let t62 := t30 t26
  let t65 := t21 e16
  let t66 := e3 e16
  let t67 := e3 e22
  let t68 := t66 e1
  let t69 := e24 e1
  let p15 : e4 = t14 := rfl
  let p16 : t14 = e4 := Eq.symm p15
  let p17 : t15 = t16 := congrFun p16 e1
  let p18 : e5 = t16 := rfl
  let p20 : t16 = e5 := Eq.symm p18
  let p21 : t15 = e5 := Eq.trans p17 p20
  let p22 : t17 = t18 := congrArg e3 p21
  let p23 : e6 = t18 := rfl
  let p25 : t18 = e6 := Eq.symm p23
  let p26 : t17 = e6 := Eq.trans p22 p25
  let p27 : t19 = t20 := congrFun p26 e2
  let p28 : e7 = t20 := rfl
  let p30 : t20 = e7 := Eq.symm p28
  let p31 : t19 = e7 := Eq.trans p27 p30
  let p33 : e8 = t21 := rfl
  let p34 : t21 = e8 := Eq.symm p33
  let p35 : t22 = t23 := congrFun p34 e2
  let p36 : e12 = t23 := rfl
  let p38 : t23 = e12 := Eq.symm p36
  let p39 : t22 = e12 := Eq.trans p35 p38
  let p40 : t24 = t25 := congr p16 p39
  let p41 : e13 = t25 := rfl
  let p43 : t25 = e13 := Eq.symm p41
  let p44 : t24 = e13 := Eq.trans p40 p43
  let p45 : t19 = t24 := assoc e0 e1 e2
  let p46 : e7 = t19 := Eq.symm p31
  let p47 : e7 = t24 := Eq.trans p46 p45
  let p48 : e7 = e13 := Eq.trans p47 p44
  let p49 : t26 = t27 := congrFun p34 e0
  let p50 : e9 = t27 := rfl
  let p52 : t27 = e9 := Eq.symm p50
  let p53 : t26 = e9 := Eq.trans p49 p52
  let p54 : t15 = t26 := comm e0 e1
  let p55 : e5 = t15 := Eq.symm p21
  let p56 : e5 = t26 := Eq.trans p55 p54
  let p57 : e5 = e9 := Eq.trans p56 p53
  let p61 : e10 = t30 := rfl
  let p62 : t30 = e10 := Eq.symm p61
  let p63 : t31 = t32 := congrFun p62 e9
  let p64 : e11 = t32 := rfl
  let p66 : t32 = e11 := Eq.symm p64
  let p67 : t31 = e11 := Eq.trans p63 p66
  let p69 : e14 = t33 := rfl
  let p70 : t33 = e14 := Eq.symm p69
  let p71 : t34 = t35 := congrFun p70 e2
  let p72 : e15 = t35 := rfl
  let p74 : t35 = e15 := Eq.symm p72
  let p75 : t34 = e15 := Eq.trans p71 p74
  let p76 : t31 = t34 := comm e2 e9
  let p77 : e11 = t31 := Eq.symm p67
  let p78 : e11 = t34 := Eq.trans p77 p76
  let p79 : e11 = e15 := Eq.trans p78 p75
  let p80 : e9 = e5 := Eq.symm p57
  let p81 : e14 = e6 := congrArg e3 p80
  let p82 : e15 = e7 := congrFun p81 e2
  let p83 : e15 = e13 := Eq.trans p82 p48
  let p84 : e11 = e13 := Eq.trans p79 p83
  let p87 : t38 = t33 := congrArg e3 p53
  let p88 : t18 = t33 := congrArg e3 p57
  let p89 : e6 = t33 := Eq.trans p23 p88
  let p90 : t33 = e6 := Eq.symm p89
  let p91 : t38 = e6 := Eq.trans p87 p90
  let p92 : t39 = t20 := congrFun p91 e2
  let p93 : t39 = e7 := Eq.trans p92 p30
  let p94 : t39 = e13 := Eq.trans p93 p48
  let p95 : t40 = t41 := congrFun p16 e2
  let p96 : e16 = t41 := rfl
  let p98 : t41 = e16 := Eq.symm p96
  let p99 : t40 = e16 := Eq.trans p95 p98
  let p100 : t42 = t43 := congr p34 p99
  let p101 : e17 = t43 := rfl
  let p103 : t43 = e17 := Eq.symm p101
  let p104 : t42 = e17 := Eq.trans p100 p103
  let p105 : t39 = t42 := assoc e1 e0 e2
  let p106 : e13 = t39 := Eq.symm p94
  let p107 : e13 = t42 := Eq.trans p106 p105
  let p108 : e13 = e17 := Eq.trans p107 p104
  let p110 : t45 = t46 := congrFun p62 e1
  let p111 : e18 = t46 := rfl
  let p113 : t46 = e18 := Eq.symm p111
  let p114 : t45 = e18 := Eq.trans p110 p113
  let p115 : t22 = t45 := comm e1 e2
  let p116 : e12 = t22 := Eq.symm p39
  let p117 : e12 = t45 := Eq.trans p116 p115
  let p118 : e12 = e18 := Eq.trans p117 p114
  let p119 : e11 = e17 := Eq.trans p84 p108
  let p120 : e7 = e17 := Eq.trans p48 p108
  let p129 : t22 = e18 := Eq.trans p39 p118
  let p130 : t52 = t53 := congrArg e3 p129
  let p131 : e19 = t53 := rfl
  let p133 : t53 = e19 := Eq.symm p131
  let p134 : t52 = e19 := Eq.trans p130 p133
  let p135 : t54 = t55 := congrFun p134 e0
  let p136 : e20 = t55 := rfl
  let p138 : t55 = e20 := Eq.symm p136
  let p139 : t54 = e20 := Eq.trans p135 p138
  let p140 : t56 = t57 := congrFun p62 e0
  let p141 : e22 = t57 := rfl
  let p143 : t57 = e22 := Eq.symm p141
  let p144 : t56 = e22 := Eq.trans p140 p143
  let p145 : t58 = t59 := congr p34 p144
  let p146 : e23 = t59 := rfl
  let p148 : t59 = e23 := Eq.symm p146
  let p149 : t58 = e23 := Eq.trans p145 p148
  let p150 : t54 = t58 := assoc e1 e2 e0
  let p151 : e20 = t54 := Eq.symm p139
  let p152 : e20 = t58 := Eq.trans p151 p150
  let p153 : e20 = e23 := Eq.trans p152 p149
  let p154 : t60 = t53 := congrArg e3 p114
  let p155 : t60 = e19 := Eq.trans p154 p133
  let p156 : t61 = t55 := congrFun p155 e0
  let p157 : t61 = e20 := Eq.trans p156 p138
  let p158 : t61 = e23 := Eq.trans p157 p153
  let p159 : t62 = t32 := congr p62 p53
  let p160 : t62 = e11 := Eq.trans p159 p66
  let p161 : t62 = e17 := Eq.trans p160 p119
  let p162 : t61 = t62 := assoc e2 e1 e0
  let p163 : e23 = t61 := Eq.symm p158
  let p164 : e20 = t61 := Eq.trans p153 p163
  let p165 : e20 = t62 := Eq.trans p164 p162
  let p166 : e20 = e17 := Eq.trans p165 p161
  let p167 : e23 = e20 := Eq.symm p153
  let p168 : e23 = e17 := Eq.trans p167 p166
  let p169 : t40 = t56 := comm e0 e2
  let p170 : e16 = t40 := Eq.symm p99
  let p171 : e16 = t56 := Eq.trans p170 p169
  let p172 : e16 = e22 := Eq.trans p171 p144
  let p176 : t65 = t59 := congr p34 p172
  let p177 : t65 = e23 := Eq.trans p176 p148
  let p178 : t65 = e17 := Eq.trans p177 p168
  let p179 : t66 = t67 := congrArg e3 p172
  let p180 : e24 = t67 := rfl
  let p182 : t67 = e24 := Eq.symm p180
  let p183 : t66 = e24 := Eq.trans p179 p182
  let p184 : t68 = t69 := congrFun p183 e1
  let p185 : e25 = t69 := rfl
  let p187 : t69 = e25 := Eq.symm p185
  let p188 : t68 = e25 := Eq.trans p184 p187
  let p189 : t65 = t68 := comm e1 e16
  let p190 : e17 = t65 := Eq.symm p178
  let p191 : e17 = t68 := Eq.trans p190 p189
  let p192 : e17 = e25 := Eq.trans p191 p188
  let p194 : e7 = e25 := Eq.trans p120 p192
  let p195 : e11 = e25 := Eq.trans p119 p192
  let p200 : e25 = e11 := Eq.symm p195
  let p201 : e7 = e11 := Eq.trans p194 p200
  exact p201
