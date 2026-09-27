theorem ac5 {α : Type} (plus : α → α → α) (x0 x1 x2 x3 x4 : α) (assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)) (comm : ∀ a b, plus a b = plus b a) : plus (plus (plus (plus x0 x1) x2) x3) x4 = plus x4 (plus x3 (plus x2 (plus x1 x0))) := by
  let e0 := x0
  let e1 := x1
  let e2 := x2
  let e3 := x3
  let e4 := x4
  let e5 := plus
  let e6 := e5 e0
  let e7 := e6 e1
  let e8 := e5 e7
  let e9 := e8 e2
  let e10 := e5 e9
  let e11 := e10 e3
  let e12 := e5 e11
  let e13 := e12 e4
  let e14 := e5 e1
  let e15 := e14 e0
  let e16 := e5 e2
  let e17 := e16 e15
  let e18 := e5 e3
  let e19 := e18 e17
  let e20 := e5 e4
  let e21 := e20 e19
  let e22 := e14 e2
  let e23 := e6 e22
  let e24 := e16 e3
  let e25 := e8 e24
  let e31 := e5 e15
  let e32 := e31 e2
  let e35 := e5 e19
  let e36 := e35 e4
  let e40 := e6 e2
  let e41 := e14 e40
  let e42 := e8 e3
  let e44 := e5 e22
  let e45 := e44 e3
  let e47 := e14 e24
  let e48 := e6 e47
  let e49 := e6 e24
  let e50 := e14 e49
  let e62 := e16 e1
  let e76 := e14 e3
  let e77 := e6 e76
  let e78 := e6 e3
  let e79 := e14 e78
  let e80 := e16 e76
  let e81 := e16 e79
  let e82 := e6 e80
  let e83 := e5 e40
  let e84 := e83 e3
  let e85 := e14 e84
  let t2 := e5 e3
  let t5 := t2 e41
  let t6 := e18 e41
  let t17 := e5 e1
  let t20 := t17 e0
  let t21 := e14 e0
  let t22 := e5 t20
  let t23 := e5 e15
  let t24 := e5 e7
  let t25 := t22 e2
  let t26 := e8 e2
  let t27 := e5 e0
  let t29 := t27 e2
  let t30 := e6 e2
  let t32 := t17 t29
  let t33 := e14 e40
  let t34 := e18 e17
  let t36 := e5 e41
  let t37 := e5 e9
  let t39 := t36 e3
  let t40 := e10 e3
  let t44 := t22 e24
  let t45 := e8 e24
  let t47 := t27 e24
  let t48 := e6 e24
  let t50 := t17 t47
  let t51 := e14 e49
  let t53 := t17 e40
  let t54 := e5 t53
  let t55 := t54 e3
  let t57 := t27 e62
  let t58 := e6 e62
  let t60 := e6 e22
  let t61 := e5 t57
  let t62 := t61 e3
  let t63 := e5 e2
  let t65 := t63 e15
  let t66 := e16 e15
  let t67 := e5 t65
  let t68 := t67 e3
  let t69 := t23 e3
  let t70 := e8 e3
  let t72 := t22 e3
  let t74 := t27 e3
  let t75 := e6 e3
  let t77 := t17 t74
  let t78 := e14 e78
  let t80 := t63 t69
  let t81 := e16 e79
  let t83 := e5 e62
  let t84 := e5 e22
  let t86 := t83 e3
  let t87 := e44 e3
  let t89 := t63 e1
  let t90 := e16 e1
  let t91 := e5 t89
  let t92 := t91 e3
  let t94 := t17 e3
  let t95 := e14 e3
  let t97 := t63 t94
  let t98 := e16 e76
  let t100 := t27 t86
  let t101 := e6 e80
  let t103 := e5 e40
  let t105 := t103 e3
  let t106 := e83 e3
  let t108 := t17 t105
  let t109 := e14 e84
  let p3 : e18 = t2 := rfl
  let p4 : t2 = e18 := Eq.symm p3
  let p7 : t5 = t6 := congrFun p4 e41
  let p8 : e17 = e32 := comm e2 e15
  let p9 : e7 = e15 := comm e0 e1
  let p10 : e15 = e7 := Eq.symm p9
  let p11 : e31 = e8 := congrArg e5 p10
  let p13 : e32 = e9 := congrFun p11 e2
  let p14 : e17 = e9 := Eq.trans p8 p13
  let p15 : e9 = e23 := assoc e0 e1 e2
  let p16 : e17 = e23 := Eq.trans p14 p15
  let p19 : e14 = t17 := rfl
  let p20 : t17 = e14 := Eq.symm p19
  let p23 : t20 = t21 := congrFun p20 e0
  let p24 : e15 = t21 := rfl
  let p26 : t21 = e15 := Eq.symm p24
  let p27 : t20 = e15 := Eq.trans p23 p26
  let p29 : t22 = t23 := congrArg e5 p27
  let p30 : e8 = t24 := rfl
  let p31 : t24 = t23 := congrArg e5 p9
  let p32 : e8 = t23 := Eq.trans p30 p31
  let p33 : t23 = e8 := Eq.symm p32
  let p34 : t22 = e8 := Eq.trans p29 p33
  let p36 : t25 = t26 := congrFun p34 e2
  let p37 : e9 = t26 := rfl
  let p39 : t26 = e9 := Eq.symm p37
  let p40 : t25 = e9 := Eq.trans p36 p39
  let p41 : t25 = e23 := Eq.trans p40 p15
  let p43 : e6 = t27 := rfl
  let p44 : t27 = e6 := Eq.symm p43
  let p46 : t29 = t30 := congrFun p44 e2
  let p47 : e40 = t30 := rfl
  let p49 : t30 = e40 := Eq.symm p47
  let p50 : t29 = e40 := Eq.trans p46 p49
  let p52 : t32 = t33 := congr p20 p50
  let p53 : e41 = t33 := rfl
  let p55 : t33 = e41 := Eq.symm p53
  let p56 : t32 = e41 := Eq.trans p52 p55
  let p58 : e23 = t25 := Eq.symm p41
  let p59 : t25 = t32 := assoc e1 e0 e2
  let p60 : e23 = t32 := Eq.trans p58 p59
  let p61 : e23 = e41 := Eq.trans p60 p56
  let p62 : e17 = e41 := Eq.trans p16 p61
  let p63 : e19 = t34 := rfl
  let p64 : t34 = t6 := congrArg e18 p62
  let p65 : e19 = t6 := Eq.trans p63 p64
  let p66 : t6 = e19 := Eq.symm p65
  let p67 : t5 = e19 := Eq.trans p7 p66
  let p70 : e9 = e41 := Eq.trans p15 p61
  let p71 : e10 = t37 := rfl
  let p72 : t37 = t36 := congrArg e5 p70
  let p73 : e10 = t36 := Eq.trans p71 p72
  let p74 : t36 = e10 := Eq.symm p73
  let p76 : t39 = t40 := congrFun p74 e3
  let p77 : e11 = t40 := rfl
  let p79 : t40 = e11 := Eq.symm p77
  let p80 : t39 = e11 := Eq.trans p76 p79
  let p81 : e11 = e25 := assoc e7 e2 e3
  let p83 : t44 = t45 := congrFun p34 e24
  let p84 : e25 = t45 := rfl
  let p86 : t45 = e25 := Eq.symm p84
  let p87 : t44 = e25 := Eq.trans p83 p86
  let p88 : e25 = e48 := assoc e0 e1 e24
  let p89 : t44 = e48 := Eq.trans p87 p88
  let p90 : t47 = t48 := congrFun p44 e24
  let p91 : e49 = t48 := rfl
  let p93 : t48 = e49 := Eq.symm p91
  let p94 : t47 = e49 := Eq.trans p90 p93
  let p96 : t50 = t51 := congr p20 p94
  let p97 : e50 = t51 := rfl
  let p99 : t51 = e50 := Eq.symm p97
  let p100 : t50 = e50 := Eq.trans p96 p99
  let p102 : e48 = t44 := Eq.symm p89
  let p103 : e25 = t44 := Eq.trans p88 p102
  let p104 : t44 = t50 := assoc e1 e0 e24
  let p105 : e25 = t50 := Eq.trans p103 p104
  let p106 : e25 = e50 := Eq.trans p105 p100
  let p107 : e11 = e50 := Eq.trans p81 p106
  let p108 : t53 = t33 := congrFun p20 e40
  let p109 : t53 = e41 := Eq.trans p108 p55
  let p110 : t54 = t36 := congrArg e5 p109
  let p111 : t54 = e10 := Eq.trans p110 p74
  let p112 : t55 = t40 := congrFun p111 e3
  let p113 : t55 = e11 := Eq.trans p112 p79
  let p115 : t57 = t58 := congrFun p44 e62
  let p116 : e22 = e62 := comm e1 e2
  let p117 : e23 = t60 := rfl
  let p118 : t60 = t58 := congrArg e6 p116
  let p119 : e23 = t58 := Eq.trans p117 p118
  let p120 : t58 = e23 := Eq.symm p119
  let p121 : t57 = e23 := Eq.trans p115 p120
  let p122 : t57 = e41 := Eq.trans p121 p61
  let p123 : t61 = t36 := congrArg e5 p122
  let p124 : t61 = e10 := Eq.trans p123 p74
  let p125 : t62 = t40 := congrFun p124 e3
  let p126 : t62 = e11 := Eq.trans p125 p79
  let p128 : e16 = t63 := rfl
  let p129 : t63 = e16 := Eq.symm p128
  let p131 : t65 = t66 := congrFun p129 e15
  let p132 : e17 = t66 := rfl
  let p134 : t66 = e17 := Eq.symm p132
  let p135 : t65 = e17 := Eq.trans p131 p134
  let p136 : t65 = e41 := Eq.trans p135 p62
  let p137 : t67 = t36 := congrArg e5 p136
  let p138 : t67 = e10 := Eq.trans p137 p74
  let p139 : t68 = t40 := congrFun p138 e3
  let p140 : t68 = e11 := Eq.trans p139 p79
  let p141 : t68 = e50 := Eq.trans p140 p107
  let p143 : t69 = t70 := congrFun p33 e3
  let p144 : e42 = t70 := rfl
  let p146 : t70 = e42 := Eq.symm p144
  let p147 : t69 = e42 := Eq.trans p143 p146
  let p148 : t72 = t70 := congrFun p34 e3
  let p149 : t72 = e42 := Eq.trans p148 p146
  let p150 : e42 = e77 := assoc e0 e1 e3
  let p151 : t72 = e77 := Eq.trans p149 p150
  let p152 : t74 = t75 := congrFun p44 e3
  let p153 : e78 = t75 := rfl
  let p155 : t75 = e78 := Eq.symm p153
  let p156 : t74 = e78 := Eq.trans p152 p155
  let p158 : t77 = t78 := congr p20 p156
  let p159 : e79 = t78 := rfl
  let p161 : t78 = e79 := Eq.symm p159
  let p162 : t77 = e79 := Eq.trans p158 p161
  let p164 : e77 = t72 := Eq.symm p151
  let p165 : e42 = t72 := Eq.trans p150 p164
  let p166 : t72 = t77 := assoc e1 e0 e3
  let p167 : e42 = t77 := Eq.trans p165 p166
  let p168 : e42 = e79 := Eq.trans p167 p162
  let p169 : t69 = e79 := Eq.trans p147 p168
  let p170 : t80 = t81 := congr p129 p169
  let p171 : e81 = t81 := rfl
  let p173 : t81 = e81 := Eq.symm p171
  let p174 : t80 = e81 := Eq.trans p170 p173
  let p176 : e50 = t68 := Eq.symm p141
  let p177 : t68 = t80 := assoc e2 e15 e3
  let p178 : e50 = t80 := Eq.trans p176 p177
  let p179 : e50 = e81 := Eq.trans p178 p174
  let p180 : e11 = e81 := Eq.trans p107 p179
  let p181 : t62 = e81 := Eq.trans p126 p180
  let p183 : e44 = t84 := rfl
  let p184 : t84 = t83 := congrArg e5 p116
  let p185 : e44 = t83 := Eq.trans p183 p184
  let p186 : t83 = e44 := Eq.symm p185
  let p188 : t86 = t87 := congrFun p186 e3
  let p189 : e45 = t87 := rfl
  let p191 : t87 = e45 := Eq.symm p189
  let p192 : t86 = e45 := Eq.trans p188 p191
  let p193 : t89 = t90 := congrFun p129 e1
  let p194 : e62 = t90 := rfl
  let p196 : t90 = e62 := Eq.symm p194
  let p197 : t89 = e62 := Eq.trans p193 p196
  let p198 : t91 = t83 := congrArg e5 p197
  let p199 : t91 = e44 := Eq.trans p198 p186
  let p200 : t92 = t87 := congrFun p199 e3
  let p201 : t92 = e45 := Eq.trans p200 p191
  let p202 : e45 = e47 := assoc e1 e2 e3
  let p203 : t92 = e47 := Eq.trans p201 p202
  let p204 : t94 = t95 := congrFun p20 e3
  let p205 : e76 = t95 := rfl
  let p207 : t95 = e76 := Eq.symm p205
  let p208 : t94 = e76 := Eq.trans p204 p207
  let p210 : t97 = t98 := congr p129 p208
  let p211 : e80 = t98 := rfl
  let p213 : t98 = e80 := Eq.symm p211
  let p214 : t97 = e80 := Eq.trans p210 p213
  let p216 : e47 = t92 := Eq.symm p203
  let p217 : e45 = t92 := Eq.trans p202 p216
  let p218 : t92 = t97 := assoc e2 e1 e3
  let p219 : e45 = t97 := Eq.trans p217 p218
  let p220 : e45 = e80 := Eq.trans p219 p214
  let p221 : t86 = e80 := Eq.trans p192 p220
  let p222 : t100 = t101 := congr p44 p221
  let p223 : e82 = t101 := rfl
  let p225 : t101 = e82 := Eq.symm p223
  let p226 : t100 = e82 := Eq.trans p222 p225
  let p228 : e81 = t62 := Eq.symm p181
  let p229 : e50 = t62 := Eq.trans p179 p228
  let p230 : t62 = t100 := assoc e0 e62 e3
  let p231 : e50 = t100 := Eq.trans p229 p230
  let p232 : e50 = e82 := Eq.trans p231 p226
  let p233 : e11 = e82 := Eq.trans p107 p232
  let p234 : t55 = e82 := Eq.trans p113 p233
  let p236 : e83 = t103 := rfl
  let p237 : t103 = e83 := Eq.symm p236
  let p239 : t105 = t106 := congrFun p237 e3
  let p240 : e84 = t106 := rfl
  let p242 : t106 = e84 := Eq.symm p240
  let p243 : t105 = e84 := Eq.trans p239 p242
  let p245 : t108 = t109 := congr p20 p243
  let p246 : e85 = t109 := rfl
  let p248 : t109 = e85 := Eq.symm p246
  let p249 : t108 = e85 := Eq.trans p245 p248
  let p251 : e82 = t55 := Eq.symm p234
  let p252 : e50 = t55 := Eq.trans p232 p251
  let p253 : t55 = t108 := assoc e1 e40 e3
  let p254 : e50 = t108 := Eq.trans p252 p253
  let p255 : e50 = e85 := Eq.trans p254 p249
  let p256 : e11 = e85 := Eq.trans p107 p255
  let p257 : t39 = e85 := Eq.trans p80 p256
  let p258 : e19 = t5 := Eq.symm p67
  let p259 : t5 = t39 := comm e3 e41
  let p260 : e19 = t39 := Eq.trans p258 p259
  let p261 : e19 = e85 := Eq.trans p260 p257
  let p262 : e85 = e50 := Eq.symm p255
  let p263 : e19 = e50 := Eq.trans p261 p262
  let p264 : e50 = e25 := Eq.symm p106
  let p265 : e19 = e25 := Eq.trans p263 p264
  let p266 : e25 = e11 := Eq.symm p81
  let p267 : e19 = e11 := Eq.trans p265 p266
  let p268 : e35 = e12 := congrArg e5 p267
  let p270 : e36 = e13 := congrFun p268 e4
  let p271 : e13 = e36 := Eq.symm p270
  let p272 : e21 = e36 := comm e4 e19
  let p273 : e36 = e21 := Eq.symm p272
  let p274 : e13 = e21 := Eq.trans p271 p273
  exact p274
