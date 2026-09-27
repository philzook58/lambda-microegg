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
  let e23 := e4 e12
  let e24 := e23 e2
  let e29 := e7 e3
  let e31 := e4 e17
  let e32 := e31 e3
  let e34 := e5 e2
  let e35 := e11 e34
  let e36 := e11 e19
  let e37 := e5 e36
  let e38 := e5 e19
  let e39 := e11 e38
  let e43 := e13 e1
  let e51 := e11 e3
  let e52 := e5 e51
  let e53 := e5 e3
  let e54 := e11 e53
  let e55 := e13 e51
  let e56 := e13 e54
  let e57 := e5 e55
  let e58 := e4 e34
  let e59 := e58 e3
  let e60 := e11 e59
  let t29 := e4 e12
  let t30 := e4 e6
  let t31 := t29 e2
  let t32 := e7 e2
  let t33 := e4 t31
  let t34 := e4 e18
  let t35 := e4 e8
  let t36 := t33 e3
  let t37 := e9 e3
  let t38 := e4 e2
  let t39 := t38 e3
  let t40 := e13 e3
  let t41 := t29 t39
  let t42 := e7 e19
  let t45 := t38 e12
  let t46 := e13 e12
  let t47 := e4 t45
  let t48 := t47 e3
  let t49 := t29 e3
  let t50 := e7 e3
  let t51 := t38 t49
  let t56 := e4 e0
  let t58 := e5 e17
  let t61 := e4 e17
  let t63 := e31 e3
  let t68 := e4 e1
  let t69 := t68 e0
  let t70 := e11 e0
  let t71 := e4 t69
  let t72 := t71 e2
  let t73 := t56 e2
  let t74 := e5 e2
  let t75 := t68 t73
  let t76 := e11 e34
  let t81 := t71 e19
  let t82 := t56 e19
  let t83 := e5 e19
  let t84 := t68 t82
  let t85 := e11 e38
  let t101 := t71 e3
  let t102 := t56 e3
  let t103 := e5 e3
  let t104 := t68 t102
  let t105 := e11 e53
  let t107 := t38 e1
  let t108 := e13 e1
  let t109 := e4 t107
  let t110 := e4 e43
  let t111 := t109 e3
  let t112 := t68 e3
  let t113 := e11 e3
  let t114 := t38 t112
  let t115 := e13 e51
  let t117 := e4 e35
  let t118 := e13 e54
  let t120 := t56 e43
  let t121 := e5 e43
  let t122 := e4 t120
  let t123 := t122 e3
  let t124 := t110 e3
  let t125 := t56 t124
  let t126 := e5 e55
  let t130 := t68 e34
  let t131 := e4 t130
  let t132 := t131 e3
  let t133 := e4 e34
  let t134 := t133 e3
  let t135 := e58 e3
  let t136 := t68 t134
  let t137 := e11 e59
  let t158 := e4 e3
  let t163 := t158 e35
  let t164 := e15 e35
  let t165 := e15 e14
  let t166 := t117 e3
  let p0 : e8 = e18 := assoc e0 e1 e2
  let p1 : e6 = e12 := comm e0 e1
  let p2 : e14 = e24 := comm e2 e12
  let p6 : e7 = t30 := rfl
  let p7 : t30 = t29 := congrArg e4 p1
  let p8 : e7 = t29 := Eq.trans p6 p7
  let p9 : t29 = e7 := Eq.symm p8
  let p12 : t31 = t32 := congrFun p9 e2
  let p13 : e8 = t32 := rfl
  let p15 : t32 = e8 := Eq.symm p13
  let p16 : t31 = e8 := Eq.trans p12 p15
  let p17 : t31 = e18 := Eq.trans p16 p0
  let p18 : t33 = t34 := congrArg e4 p17
  let p19 : e9 = t35 := rfl
  let p20 : t35 = t34 := congrArg e4 p0
  let p21 : e9 = t34 := Eq.trans p19 p20
  let p22 : t34 = e9 := Eq.symm p21
  let p23 : t33 = e9 := Eq.trans p18 p22
  let p26 : t36 = t37 := congrFun p23 e3
  let p27 : e10 = t37 := rfl
  let p29 : t37 = e10 := Eq.symm p27
  let p30 : t36 = e10 := Eq.trans p26 p29
  let p33 : e13 = t38 := rfl
  let p34 : t38 = e13 := Eq.symm p33
  let p36 : t39 = t40 := congrFun p34 e3
  let p37 : e19 = t40 := rfl
  let p39 : t40 = e19 := Eq.symm p37
  let p40 : t39 = e19 := Eq.trans p36 p39
  let p42 : t41 = t42 := congr p9 p40
  let p43 : e20 = t42 := rfl
  let p45 : t42 = e20 := Eq.symm p43
  let p46 : t41 = e20 := Eq.trans p42 p45
  let p48 : t36 = t41 := assoc e12 e2 e3
  let p49 : e10 = t36 := Eq.symm p30
  let p50 : e10 = t41 := Eq.trans p49 p48
  let p51 : e10 = e20 := Eq.trans p50 p46
  let p52 : t45 = t46 := congrFun p34 e12
  let p53 : e14 = t46 := rfl
  let p55 : t46 = e14 := Eq.symm p53
  let p56 : t45 = e14 := Eq.trans p52 p55
  let p57 : e12 = e6 := Eq.symm p1
  let p58 : e23 = e7 := congrArg e4 p57
  let p59 : e24 = e8 := congrFun p58 e2
  let p60 : e14 = e8 := Eq.trans p2 p59
  let p61 : e14 = e18 := Eq.trans p60 p0
  let p68 : t49 = t50 := congrFun p9 e3
  let p69 : e29 = t50 := rfl
  let p71 : t50 = e29 := Eq.symm p69
  let p72 : t49 = e29 := Eq.trans p68 p71
  let p80 : t48 = t51 := assoc e2 e12 e3
  let p87 : e5 = t56 := rfl
  let p88 : t56 = e5 := Eq.symm p87
  let p92 : e18 = t58 := rfl
  let p103 : e31 = t61 := rfl
  let p107 : e32 = t63 := rfl
  let p109 : t63 = e32 := Eq.symm p107
  let p125 : e11 = t68 := rfl
  let p126 : t68 = e11 := Eq.symm p125
  let p128 : t69 = t70 := congrFun p126 e0
  let p129 : e12 = t70 := rfl
  let p131 : t70 = e12 := Eq.symm p129
  let p132 : t69 = e12 := Eq.trans p128 p131
  let p133 : t71 = t29 := congrArg e4 p132
  let p134 : t71 = e7 := Eq.trans p133 p9
  let p135 : t72 = t32 := congrFun p134 e2
  let p136 : t72 = e8 := Eq.trans p135 p15
  let p137 : t72 = e18 := Eq.trans p136 p0
  let p138 : t73 = t74 := congrFun p88 e2
  let p139 : e34 = t74 := rfl
  let p141 : t74 = e34 := Eq.symm p139
  let p142 : t73 = e34 := Eq.trans p138 p141
  let p144 : t75 = t76 := congr p126 p142
  let p145 : e35 = t76 := rfl
  let p147 : t76 = e35 := Eq.symm p145
  let p148 : t75 = e35 := Eq.trans p144 p147
  let p150 : t72 = t75 := assoc e1 e0 e2
  let p151 : e18 = t72 := Eq.symm p137
  let p152 : e18 = t75 := Eq.trans p151 p150
  let p153 : e18 = e35 := Eq.trans p152 p148
  let p154 : e20 = e37 := assoc e0 e1 e19
  let p155 : t81 = t42 := congrFun p134 e19
  let p156 : t81 = e20 := Eq.trans p155 p45
  let p157 : t81 = e37 := Eq.trans p156 p154
  let p158 : t82 = t83 := congrFun p88 e19
  let p159 : e38 = t83 := rfl
  let p161 : t83 = e38 := Eq.symm p159
  let p162 : t82 = e38 := Eq.trans p158 p161
  let p164 : t84 = t85 := congr p126 p162
  let p165 : e39 = t85 := rfl
  let p167 : t85 = e39 := Eq.symm p165
  let p168 : t84 = e39 := Eq.trans p164 p167
  let p170 : t81 = t84 := assoc e1 e0 e19
  let p171 : e37 = t81 := Eq.symm p157
  let p172 : e20 = t81 := Eq.trans p154 p171
  let p173 : e20 = t84 := Eq.trans p172 p170
  let p174 : e20 = e39 := Eq.trans p173 p168
  let p175 : e17 = e43 := comm e1 e2
  let p177 : e29 = e52 := assoc e0 e1 e3
  let p178 : t101 = t50 := congrFun p134 e3
  let p179 : t101 = e29 := Eq.trans p178 p71
  let p180 : t101 = e52 := Eq.trans p179 p177
  let p181 : t102 = t103 := congrFun p88 e3
  let p182 : e53 = t103 := rfl
  let p184 : t103 = e53 := Eq.symm p182
  let p185 : t102 = e53 := Eq.trans p181 p184
  let p187 : t104 = t105 := congr p126 p185
  let p188 : e54 = t105 := rfl
  let p190 : t105 = e54 := Eq.symm p188
  let p191 : t104 = e54 := Eq.trans p187 p190
  let p193 : t101 = t104 := assoc e1 e0 e3
  let p194 : e52 = t101 := Eq.symm p180
  let p195 : e29 = t101 := Eq.trans p177 p194
  let p196 : e29 = t104 := Eq.trans p195 p193
  let p197 : e29 = e54 := Eq.trans p196 p191
  let p198 : e32 = e36 := assoc e1 e2 e3
  let p199 : t107 = t108 := congrFun p34 e1
  let p200 : e43 = t108 := rfl
  let p202 : t108 = e43 := Eq.symm p200
  let p203 : t107 = e43 := Eq.trans p199 p202
  let p205 : t109 = t110 := congrArg e4 p203
  let p206 : t61 = t110 := congrArg e4 p175
  let p207 : e31 = t110 := Eq.trans p103 p206
  let p208 : t110 = e31 := Eq.symm p207
  let p209 : t109 = e31 := Eq.trans p205 p208
  let p210 : t111 = t63 := congrFun p209 e3
  let p211 : t111 = e32 := Eq.trans p210 p109
  let p212 : t111 = e36 := Eq.trans p211 p198
  let p213 : t112 = t113 := congrFun p126 e3
  let p214 : e51 = t113 := rfl
  let p216 : t113 = e51 := Eq.symm p214
  let p217 : t112 = e51 := Eq.trans p213 p216
  let p219 : t114 = t115 := congr p34 p217
  let p220 : e55 = t115 := rfl
  let p222 : t115 = e55 := Eq.symm p220
  let p223 : t114 = e55 := Eq.trans p219 p222
  let p225 : t111 = t114 := assoc e2 e1 e3
  let p226 : e36 = t111 := Eq.symm p212
  let p227 : e32 = t111 := Eq.trans p198 p226
  let p228 : e32 = t114 := Eq.trans p227 p225
  let p229 : e32 = e55 := Eq.trans p228 p223
  let p230 : e14 = e35 := Eq.trans p61 p153
  let p231 : t45 = e35 := Eq.trans p56 p230
  let p232 : t47 = t117 := congrArg e4 p231
  let p233 : e8 = e35 := Eq.trans p0 p153
  let p234 : t35 = t117 := congrArg e4 p233
  let p235 : e9 = t117 := Eq.trans p19 p234
  let p236 : t117 = e9 := Eq.symm p235
  let p237 : t47 = e9 := Eq.trans p232 p236
  let p238 : t48 = t37 := congrFun p237 e3
  let p239 : t48 = e10 := Eq.trans p238 p29
  let p240 : e10 = e39 := Eq.trans p51 p174
  let p241 : t48 = e39 := Eq.trans p239 p240
  let p242 : t49 = e54 := Eq.trans p72 p197
  let p243 : t51 = t118 := congr p34 p242
  let p244 : e56 = t118 := rfl
  let p246 : t118 = e56 := Eq.symm p244
  let p247 : t51 = e56 := Eq.trans p243 p246
  let p249 : e39 = t48 := Eq.symm p241
  let p250 : e39 = t51 := Eq.trans p249 p80
  let p251 : e39 = e56 := Eq.trans p250 p247
  let p252 : t120 = t121 := congrFun p88 e43
  let p253 : t58 = t121 := congrArg e5 p175
  let p254 : e18 = t121 := Eq.trans p92 p253
  let p255 : t121 = e18 := Eq.symm p254
  let p256 : t120 = e18 := Eq.trans p252 p255
  let p257 : t120 = e35 := Eq.trans p256 p153
  let p258 : t122 = t117 := congrArg e4 p257
  let p259 : t122 = e9 := Eq.trans p258 p236
  let p260 : t123 = t37 := congrFun p259 e3
  let p261 : t123 = e10 := Eq.trans p260 p29
  let p262 : e10 = e56 := Eq.trans p240 p251
  let p263 : t123 = e56 := Eq.trans p261 p262
  let p265 : t124 = t63 := congrFun p208 e3
  let p266 : t124 = e32 := Eq.trans p265 p109
  let p267 : t124 = e55 := Eq.trans p266 p229
  let p268 : t125 = t126 := congr p88 p267
  let p269 : e57 = t126 := rfl
  let p271 : t126 = e57 := Eq.symm p269
  let p272 : t125 = e57 := Eq.trans p268 p271
  let p274 : t123 = t125 := assoc e0 e43 e3
  let p275 : e56 = t123 := Eq.symm p263
  let p276 : e39 = t123 := Eq.trans p251 p275
  let p277 : e39 = t125 := Eq.trans p276 p274
  let p278 : e39 = e57 := Eq.trans p277 p272
  let p279 : t130 = t76 := congrFun p126 e34
  let p280 : t130 = e35 := Eq.trans p279 p147
  let p281 : t131 = t117 := congrArg e4 p280
  let p282 : t131 = e9 := Eq.trans p281 p236
  let p283 : t132 = t37 := congrFun p282 e3
  let p284 : t132 = e10 := Eq.trans p283 p29
  let p285 : e10 = e57 := Eq.trans p240 p278
  let p286 : t132 = e57 := Eq.trans p284 p285
  let p288 : e58 = t133 := rfl
  let p289 : t133 = e58 := Eq.symm p288
  let p291 : t134 = t135 := congrFun p289 e3
  let p292 : e59 = t135 := rfl
  let p294 : t135 = e59 := Eq.symm p292
  let p295 : t134 = e59 := Eq.trans p291 p294
  let p297 : t136 = t137 := congr p126 p295
  let p298 : e60 = t137 := rfl
  let p300 : t137 = e60 := Eq.symm p298
  let p301 : t136 = e60 := Eq.trans p297 p300
  let p303 : t132 = t136 := assoc e1 e34 e3
  let p304 : e57 = t132 := Eq.symm p286
  let p305 : e39 = t132 := Eq.trans p278 p304
  let p306 : e39 = t136 := Eq.trans p305 p303
  let p307 : e39 = e60 := Eq.trans p306 p301
  let p367 : e15 = t158 := rfl
  let p368 : t158 = e15 := Eq.symm p367
  let p387 : t163 = t164 := congrFun p368 e35
  let p388 : e16 = t165 := rfl
  let p389 : t165 = t164 := congrArg e15 p230
  let p390 : e16 = t164 := Eq.trans p388 p389
  let p391 : t164 = e16 := Eq.symm p390
  let p392 : t163 = e16 := Eq.trans p387 p391
  let p395 : t166 = t37 := congrFun p236 e3
  let p396 : t166 = e10 := Eq.trans p395 p29
  let p397 : e10 = e60 := Eq.trans p240 p307
  let p398 : t166 = e60 := Eq.trans p396 p397
  let p399 : t163 = t166 := comm e3 e35
  let p400 : e16 = t163 := Eq.symm p392
  let p401 : e16 = t166 := Eq.trans p400 p399
  let p402 : e16 = e60 := Eq.trans p401 p398
  let p972 : e60 = e16 := Eq.symm p402
  let p973 : e10 = e16 := Eq.trans p397 p972
  exact p973
