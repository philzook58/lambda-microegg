theorem ac4 {α : Type} (plus : α → α → α) (x0 x1 x2 x3 : α) (assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)) (comm : ∀ a b, plus a b = plus b a) : plus (plus (plus x0 x1) x2) x3 = plus x3 (plus x2 (plus x1 x0)) := by
  let e0 := x0
  let e1 := x1
  let e2 := x2
  let e3 := x3
  let e4 := plus
  let e5 := e4 e0
  let e6 := e5 e1
  let e7 := e4 e6
  let e8 := e7 e2
  let e9 := e4 e8
  let e10 := e9 e3
  let e11 := e4 e1
  let e12 := e11 e0
  let e13 := e4 e2
  let e14 := e13 e12
  let e15 := e4 e3
  let e16 := e15 e14
  let e17 := e11 e2
  let e18 := e5 e17
  let e19 := e13 e3
  let e20 := e7 e19
  let e22 := e4 e12
  let e23 := e22 e2
  let e26 := e5 e2
  let e27 := e11 e26
  let e28 := e7 e3
  let e30 := e4 e17
  let e31 := e30 e3
  let e33 := e11 e19
  let e34 := e5 e33
  let e35 := e5 e19
  let e36 := e11 e35
  let e39 := e13 e1
  let e46 := e11 e3
  let e47 := e5 e46
  let e48 := e5 e3
  let e49 := e11 e48
  let e50 := e13 e46
  let e51 := e13 e49
  let e52 := e5 e50
  let e53 := e4 e26
  let e54 := e53 e3
  let e55 := e11 e54
  let t4 := e4 e1
  let t7 := t4 e0
  let t8 := e11 e0
  let t10 := e4 t7
  let t11 := e4 e12
  let t13 := e4 e6
  let t16 := t10 e19
  let t17 := e7 e19
  let t19 := e4 e0
  let t21 := t19 e19
  let t22 := e5 e19
  let t24 := t4 t21
  let t25 := e11 e35
  let t28 := t4 e26
  let t29 := e11 e26
  let t31 := e4 t28
  let t32 := e4 e27
  let t36 := t10 e2
  let t37 := e7 e2
  let t38 := t19 e2
  let t39 := e5 e2
  let t40 := t4 t38
  let t41 := e4 e8
  let t44 := t31 e3
  let t45 := e9 e3
  let t47 := t19 e39
  let t48 := e5 e39
  let t50 := e5 e17
  let t51 := e4 t47
  let t52 := t51 e3
  let t53 := e4 e2
  let t55 := t53 e12
  let t56 := e13 e12
  let t60 := e4 t55
  let t61 := t60 e3
  let t62 := t11 e3
  let t63 := e7 e3
  let t65 := t10 e3
  let t67 := t19 e3
  let t68 := e5 e3
  let t70 := t4 t67
  let t71 := e11 e48
  let t73 := t53 t62
  let t74 := e13 e49
  let t76 := e4 e39
  let t77 := e4 e17
  let t79 := t76 e3
  let t80 := e30 e3
  let t82 := t53 e1
  let t83 := e13 e1
  let t84 := e4 t82
  let t85 := t84 e3
  let t87 := t4 e3
  let t88 := e11 e3
  let t90 := t53 t87
  let t91 := e13 e46
  let t93 := t19 t79
  let t94 := e5 e50
  let t96 := e4 e26
  let t98 := t96 e3
  let t99 := e53 e3
  let t101 := t4 t98
  let t102 := e11 e54
  let t104 := e4 e3
  let t106 := t104 e27
  let t107 := e15 e27
  let t108 := e15 e14
  let t110 := t32 e3
  let p0 : e10 = e20 := assoc e6 e2 e3
  let p4 : e11 = t4 := rfl
  let p5 : t4 = e11 := Eq.symm p4
  let p8 : t7 = t8 := congrFun p5 e0
  let p9 : e12 = t8 := rfl
  let p11 : t8 = e12 := Eq.symm p9
  let p12 : t7 = e12 := Eq.trans p8 p11
  let p14 : t10 = t11 := congrArg e4 p12
  let p15 : e6 = e12 := comm e0 e1
  let p16 : e7 = t13 := rfl
  let p17 : t13 = t11 := congrArg e4 p15
  let p18 : e7 = t11 := Eq.trans p16 p17
  let p19 : t11 = e7 := Eq.symm p18
  let p20 : t10 = e7 := Eq.trans p14 p19
  let p23 : t16 = t17 := congrFun p20 e19
  let p24 : e20 = t17 := rfl
  let p26 : t17 = e20 := Eq.symm p24
  let p27 : t16 = e20 := Eq.trans p23 p26
  let p28 : e20 = e34 := assoc e0 e1 e19
  let p29 : t16 = e34 := Eq.trans p27 p28
  let p31 : e5 = t19 := rfl
  let p32 : t19 = e5 := Eq.symm p31
  let p34 : t21 = t22 := congrFun p32 e19
  let p35 : e35 = t22 := rfl
  let p37 : t22 = e35 := Eq.symm p35
  let p38 : t21 = e35 := Eq.trans p34 p37
  let p40 : t24 = t25 := congr p5 p38
  let p41 : e36 = t25 := rfl
  let p43 : t25 = e36 := Eq.symm p41
  let p44 : t24 = e36 := Eq.trans p40 p43
  let p46 : e34 = t16 := Eq.symm p29
  let p47 : e20 = t16 := Eq.trans p28 p46
  let p48 : t16 = t24 := assoc e1 e0 e19
  let p49 : e20 = t24 := Eq.trans p47 p48
  let p50 : e20 = e36 := Eq.trans p49 p44
  let p51 : e10 = e36 := Eq.trans p0 p50
  let p53 : t28 = t29 := congrFun p5 e26
  let p54 : e27 = t29 := rfl
  let p56 : t29 = e27 := Eq.symm p54
  let p57 : t28 = e27 := Eq.trans p53 p56
  let p59 : t31 = t32 := congrArg e4 p57
  let p60 : e8 = e18 := assoc e0 e1 e2
  let p62 : t36 = t37 := congrFun p20 e2
  let p63 : e8 = t37 := rfl
  let p65 : t37 = e8 := Eq.symm p63
  let p66 : t36 = e8 := Eq.trans p62 p65
  let p67 : t36 = e18 := Eq.trans p66 p60
  let p68 : t38 = t39 := congrFun p32 e2
  let p69 : e26 = t39 := rfl
  let p71 : t39 = e26 := Eq.symm p69
  let p72 : t38 = e26 := Eq.trans p68 p71
  let p73 : t40 = t29 := congr p5 p72
  let p74 : t40 = e27 := Eq.trans p73 p56
  let p76 : e18 = t36 := Eq.symm p67
  let p77 : t36 = t40 := assoc e1 e0 e2
  let p78 : e18 = t40 := Eq.trans p76 p77
  let p79 : e18 = e27 := Eq.trans p78 p74
  let p80 : e8 = e27 := Eq.trans p60 p79
  let p81 : e9 = t41 := rfl
  let p82 : t41 = t32 := congrArg e4 p80
  let p83 : e9 = t32 := Eq.trans p81 p82
  let p84 : t32 = e9 := Eq.symm p83
  let p85 : t31 = e9 := Eq.trans p59 p84
  let p88 : t44 = t45 := congrFun p85 e3
  let p89 : e10 = t45 := rfl
  let p91 : t45 = e10 := Eq.symm p89
  let p92 : t44 = e10 := Eq.trans p88 p91
  let p94 : t47 = t48 := congrFun p32 e39
  let p95 : e17 = e39 := comm e1 e2
  let p96 : e18 = t50 := rfl
  let p97 : t50 = t48 := congrArg e5 p95
  let p98 : e18 = t48 := Eq.trans p96 p97
  let p99 : t48 = e18 := Eq.symm p98
  let p100 : t47 = e18 := Eq.trans p94 p99
  let p101 : t47 = e27 := Eq.trans p100 p79
  let p102 : t51 = t32 := congrArg e4 p101
  let p103 : t51 = e9 := Eq.trans p102 p84
  let p104 : t52 = t45 := congrFun p103 e3
  let p105 : t52 = e10 := Eq.trans p104 p91
  let p107 : e13 = t53 := rfl
  let p108 : t53 = e13 := Eq.symm p107
  let p110 : t55 = t56 := congrFun p108 e12
  let p111 : e14 = t56 := rfl
  let p113 : t56 = e14 := Eq.symm p111
  let p114 : t55 = e14 := Eq.trans p110 p113
  let p115 : e14 = e23 := comm e2 e12
  let p116 : e12 = e6 := Eq.symm p15
  let p117 : e22 = e7 := congrArg e4 p116
  let p118 : e23 = e8 := congrFun p117 e2
  let p119 : e14 = e8 := Eq.trans p115 p118
  let p120 : e14 = e18 := Eq.trans p119 p60
  let p121 : e14 = e27 := Eq.trans p120 p79
  let p122 : t55 = e27 := Eq.trans p114 p121
  let p123 : t60 = t32 := congrArg e4 p122
  let p124 : t60 = e9 := Eq.trans p123 p84
  let p125 : t61 = t45 := congrFun p124 e3
  let p126 : t61 = e10 := Eq.trans p125 p91
  let p127 : t61 = e36 := Eq.trans p126 p51
  let p129 : t62 = t63 := congrFun p19 e3
  let p130 : e28 = t63 := rfl
  let p132 : t63 = e28 := Eq.symm p130
  let p133 : t62 = e28 := Eq.trans p129 p132
  let p134 : t65 = t63 := congrFun p20 e3
  let p135 : t65 = e28 := Eq.trans p134 p132
  let p136 : e28 = e47 := assoc e0 e1 e3
  let p137 : t65 = e47 := Eq.trans p135 p136
  let p138 : t67 = t68 := congrFun p32 e3
  let p139 : e48 = t68 := rfl
  let p141 : t68 = e48 := Eq.symm p139
  let p142 : t67 = e48 := Eq.trans p138 p141
  let p144 : t70 = t71 := congr p5 p142
  let p145 : e49 = t71 := rfl
  let p147 : t71 = e49 := Eq.symm p145
  let p148 : t70 = e49 := Eq.trans p144 p147
  let p150 : e47 = t65 := Eq.symm p137
  let p151 : e28 = t65 := Eq.trans p136 p150
  let p152 : t65 = t70 := assoc e1 e0 e3
  let p153 : e28 = t70 := Eq.trans p151 p152
  let p154 : e28 = e49 := Eq.trans p153 p148
  let p155 : t62 = e49 := Eq.trans p133 p154
  let p156 : t73 = t74 := congr p108 p155
  let p157 : e51 = t74 := rfl
  let p159 : t74 = e51 := Eq.symm p157
  let p160 : t73 = e51 := Eq.trans p156 p159
  let p162 : e36 = t61 := Eq.symm p127
  let p163 : t61 = t73 := assoc e2 e12 e3
  let p164 : e36 = t73 := Eq.trans p162 p163
  let p165 : e36 = e51 := Eq.trans p164 p160
  let p166 : e10 = e51 := Eq.trans p51 p165
  let p167 : t52 = e51 := Eq.trans p105 p166
  let p169 : e30 = t77 := rfl
  let p170 : t77 = t76 := congrArg e4 p95
  let p171 : e30 = t76 := Eq.trans p169 p170
  let p172 : t76 = e30 := Eq.symm p171
  let p174 : t79 = t80 := congrFun p172 e3
  let p175 : e31 = t80 := rfl
  let p177 : t80 = e31 := Eq.symm p175
  let p178 : t79 = e31 := Eq.trans p174 p177
  let p179 : t82 = t83 := congrFun p108 e1
  let p180 : e39 = t83 := rfl
  let p182 : t83 = e39 := Eq.symm p180
  let p183 : t82 = e39 := Eq.trans p179 p182
  let p184 : t84 = t76 := congrArg e4 p183
  let p185 : t84 = e30 := Eq.trans p184 p172
  let p186 : t85 = t80 := congrFun p185 e3
  let p187 : t85 = e31 := Eq.trans p186 p177
  let p188 : e31 = e33 := assoc e1 e2 e3
  let p189 : t85 = e33 := Eq.trans p187 p188
  let p190 : t87 = t88 := congrFun p5 e3
  let p191 : e46 = t88 := rfl
  let p193 : t88 = e46 := Eq.symm p191
  let p194 : t87 = e46 := Eq.trans p190 p193
  let p196 : t90 = t91 := congr p108 p194
  let p197 : e50 = t91 := rfl
  let p199 : t91 = e50 := Eq.symm p197
  let p200 : t90 = e50 := Eq.trans p196 p199
  let p202 : e33 = t85 := Eq.symm p189
  let p203 : e31 = t85 := Eq.trans p188 p202
  let p204 : t85 = t90 := assoc e2 e1 e3
  let p205 : e31 = t90 := Eq.trans p203 p204
  let p206 : e31 = e50 := Eq.trans p205 p200
  let p207 : t79 = e50 := Eq.trans p178 p206
  let p208 : t93 = t94 := congr p32 p207
  let p209 : e52 = t94 := rfl
  let p211 : t94 = e52 := Eq.symm p209
  let p212 : t93 = e52 := Eq.trans p208 p211
  let p214 : e51 = t52 := Eq.symm p167
  let p215 : e36 = t52 := Eq.trans p165 p214
  let p216 : t52 = t93 := assoc e0 e39 e3
  let p217 : e36 = t93 := Eq.trans p215 p216
  let p218 : e36 = e52 := Eq.trans p217 p212
  let p219 : e10 = e52 := Eq.trans p51 p218
  let p220 : t44 = e52 := Eq.trans p92 p219
  let p222 : e53 = t96 := rfl
  let p223 : t96 = e53 := Eq.symm p222
  let p225 : t98 = t99 := congrFun p223 e3
  let p226 : e54 = t99 := rfl
  let p228 : t99 = e54 := Eq.symm p226
  let p229 : t98 = e54 := Eq.trans p225 p228
  let p231 : t101 = t102 := congr p5 p229
  let p232 : e55 = t102 := rfl
  let p234 : t102 = e55 := Eq.symm p232
  let p235 : t101 = e55 := Eq.trans p231 p234
  let p237 : e52 = t44 := Eq.symm p220
  let p238 : e36 = t44 := Eq.trans p218 p237
  let p239 : t44 = t101 := assoc e1 e26 e3
  let p240 : e36 = t101 := Eq.trans p238 p239
  let p241 : e36 = e55 := Eq.trans p240 p235
  let p242 : e10 = e55 := Eq.trans p51 p241
  let p244 : e15 = t104 := rfl
  let p245 : t104 = e15 := Eq.symm p244
  let p247 : t106 = t107 := congrFun p245 e27
  let p248 : e16 = t108 := rfl
  let p249 : t108 = t107 := congrArg e15 p121
  let p250 : e16 = t107 := Eq.trans p248 p249
  let p251 : t107 = e16 := Eq.symm p250
  let p252 : t106 = e16 := Eq.trans p247 p251
  let p255 : t110 = t45 := congrFun p84 e3
  let p256 : t110 = e10 := Eq.trans p255 p91
  let p257 : t110 = e55 := Eq.trans p256 p242
  let p258 : e16 = t106 := Eq.symm p252
  let p259 : t106 = t110 := comm e3 e27
  let p260 : e16 = t110 := Eq.trans p258 p259
  let p261 : e16 = e55 := Eq.trans p260 p257
  let p262 : e55 = e16 := Eq.symm p261
  let p263 : e10 = e16 := Eq.trans p242 p262
  exact p263
