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
  let e26 := e5 e23
  let e28 := e18 e4
  let e29 := e26 e28
  let e32 := e5 e15
  let e33 := e32 e2
  let e35 := e20 e11
  let e39 := e5 e19
  let e40 := e39 e4
  let e43 := e5 e22
  let e46 := e6 e2
  let e47 := e14 e46
  let e48 := e14 e24
  let e49 := e6 e48
  let e50 := e6 e24
  let e51 := e14 e50
  let e52 := e16 e28
  let e53 := e8 e52
  let e54 := e5 e47
  let e56 := e8 e28
  let e57 := e16 e56
  let e58 := e43 e28
  let e59 := e6 e58
  let e63 := e54 e4
  let e64 := e18 e63
  let e68 := e16 e1
  let e76 := e20 e3
  let e77 := e5 e76
  let e78 := e77 e47
  let e83 := e5 e46
  let e84 := e83 e76
  let e85 := e14 e84
  let e109 := e14 e52
  let e110 := e6 e109
  let e111 := e6 e52
  let e112 := e14 e111
  let e130 := e20 e47
  let e131 := e18 e130
  let t41 := e5 e15
  let t42 := e5 e7
  let t43 := t41 e2
  let t44 := e8 e2
  let t45 := e5 t43
  let t46 := e5 e23
  let t47 := e5 e9
  let t48 := t45 e3
  let t49 := e10 e3
  let t50 := e5 e2
  let t51 := t50 e3
  let t52 := e16 e3
  let t53 := t41 t51
  let t54 := e8 e24
  let t57 := t50 e15
  let t58 := e16 e15
  let t59 := e5 t57
  let t68 := e5 e0
  let t70 := e6 e22
  let t73 := e5 e22
  let t80 := e5 e1
  let t81 := t80 e0
  let t82 := e14 e0
  let t83 := e5 t81
  let t84 := t83 e2
  let t85 := t68 e2
  let t86 := e6 e2
  let t87 := t80 t85
  let t88 := e14 e46
  let t93 := t83 e24
  let t94 := t68 e24
  let t95 := e6 e24
  let t96 := t80 t94
  let t97 := e14 e50
  let t129 := e5 e47
  let t130 := t45 e76
  let t131 := e10 e76
  let t132 := e26 e28
  let t133 := t50 e76
  let t134 := e16 e76
  let t135 := e16 e28
  let t136 := t41 t133
  let t137 := e8 e52
  let t138 := t59 e76
  let t139 := t41 e76
  let t140 := e8 e76
  let t141 := e8 e28
  let t142 := t50 t139
  let t143 := e16 e56
  let t144 := t68 e68
  let t145 := e6 e68
  let t146 := e5 t144
  let t147 := t146 e76
  let t148 := e5 e68
  let t149 := t148 e76
  let t150 := e43 e76
  let t151 := e43 e28
  let t152 := t68 t149
  let t153 := e6 e58
  let t157 := t80 e46
  let t158 := e5 t157
  let t159 := t158 e76
  let t160 := e5 e46
  let t161 := t160 e76
  let t162 := e83 e76
  let t163 := t80 t161
  let t164 := e14 e84
  let t165 := t129 e3
  let t166 := e5 t165
  let t167 := e5 e51
  let t168 := e5 e11
  let t169 := t166 e4
  let t170 := e12 e4
  let t171 := e5 e3
  let t172 := t171 e4
  let t173 := e18 e4
  let t174 := t129 t172
  let t231 := t171 e47
  let t232 := e18 e47
  let t233 := e18 e17
  let t234 := e5 t231
  let t235 := e5 e19
  let t236 := t234 e4
  let t237 := e39 e4
  let t238 := t129 e4
  let t239 := e10 e4
  let t240 := e54 e4
  let t241 := t171 t238
  let t242 := e18 e63
  let t279 := t83 e52
  let t280 := t68 e52
  let t281 := e6 e52
  let t282 := t80 t280
  let t283 := e14 e111
  let t356 := e5 t172
  let t357 := e5 e76
  let t358 := t356 e47
  let t359 := e77 e47
  let t360 := e5 e4
  let t361 := t360 e47
  let t362 := e20 e47
  let t363 := t171 t361
  let t364 := e18 e130
  let t365 := t360 e3
  let t366 := e20 e3
  let t367 := e5 t365
  let t368 := t367 e47
  let t369 := t360 t231
  let t370 := e20 e19
  let t371 := t129 e76
  let t372 := t357 e47
  let p0 : e9 = e23 := assoc e0 e1 e2
  let p1 : e7 = e15 := comm e0 e1
  let p2 : e13 = e35 := comm e11 e4
  let p3 : e17 = e33 := comm e2 e15
  let p4 : e21 = e40 := comm e4 e19
  let p8 : e8 = t42 := rfl
  let p9 : t42 = t41 := congrArg e5 p1
  let p10 : e8 = t41 := Eq.trans p8 p9
  let p11 : t41 = e8 := Eq.symm p10
  let p14 : t43 = t44 := congrFun p11 e2
  let p15 : e9 = t44 := rfl
  let p17 : t44 = e9 := Eq.symm p15
  let p18 : t43 = e9 := Eq.trans p14 p17
  let p19 : t43 = e23 := Eq.trans p18 p0
  let p20 : t45 = t46 := congrArg e5 p19
  let p21 : e10 = t47 := rfl
  let p22 : t47 = t46 := congrArg e5 p0
  let p23 : e10 = t46 := Eq.trans p21 p22
  let p24 : t46 = e10 := Eq.symm p23
  let p25 : t45 = e10 := Eq.trans p20 p24
  let p28 : t48 = t49 := congrFun p25 e3
  let p29 : e11 = t49 := rfl
  let p31 : t49 = e11 := Eq.symm p29
  let p32 : t48 = e11 := Eq.trans p28 p31
  let p35 : e16 = t50 := rfl
  let p36 : t50 = e16 := Eq.symm p35
  let p38 : t51 = t52 := congrFun p36 e3
  let p39 : e24 = t52 := rfl
  let p41 : t52 = e24 := Eq.symm p39
  let p42 : t51 = e24 := Eq.trans p38 p41
  let p44 : t53 = t54 := congr p11 p42
  let p45 : e25 = t54 := rfl
  let p47 : t54 = e25 := Eq.symm p45
  let p48 : t53 = e25 := Eq.trans p44 p47
  let p50 : t48 = t53 := assoc e15 e2 e3
  let p51 : e11 = t48 := Eq.symm p32
  let p52 : e11 = t53 := Eq.trans p51 p50
  let p53 : e11 = e25 := Eq.trans p52 p48
  let p54 : t57 = t58 := congrFun p36 e15
  let p55 : e17 = t58 := rfl
  let p57 : t58 = e17 := Eq.symm p55
  let p58 : t57 = e17 := Eq.trans p54 p57
  let p59 : e15 = e7 := Eq.symm p1
  let p60 : e32 = e8 := congrArg e5 p59
  let p61 : e33 = e9 := congrFun p60 e2
  let p62 : e17 = e9 := Eq.trans p3 p61
  let p63 : e17 = e23 := Eq.trans p62 p0
  let p89 : e6 = t68 := rfl
  let p90 : t68 = e6 := Eq.symm p89
  let p94 : e23 = t70 := rfl
  let p105 : e43 = t73 := rfl
  let p127 : e14 = t80 := rfl
  let p128 : t80 = e14 := Eq.symm p127
  let p130 : t81 = t82 := congrFun p128 e0
  let p131 : e15 = t82 := rfl
  let p133 : t82 = e15 := Eq.symm p131
  let p134 : t81 = e15 := Eq.trans p130 p133
  let p135 : t83 = t41 := congrArg e5 p134
  let p136 : t83 = e8 := Eq.trans p135 p11
  let p137 : t84 = t44 := congrFun p136 e2
  let p138 : t84 = e9 := Eq.trans p137 p17
  let p139 : t84 = e23 := Eq.trans p138 p0
  let p140 : t85 = t86 := congrFun p90 e2
  let p141 : e46 = t86 := rfl
  let p143 : t86 = e46 := Eq.symm p141
  let p144 : t85 = e46 := Eq.trans p140 p143
  let p146 : t87 = t88 := congr p128 p144
  let p147 : e47 = t88 := rfl
  let p149 : t88 = e47 := Eq.symm p147
  let p150 : t87 = e47 := Eq.trans p146 p149
  let p152 : t84 = t87 := assoc e1 e0 e2
  let p153 : e23 = t84 := Eq.symm p139
  let p154 : e23 = t87 := Eq.trans p153 p152
  let p155 : e23 = e47 := Eq.trans p154 p150
  let p156 : e25 = e49 := assoc e0 e1 e24
  let p157 : t93 = t54 := congrFun p136 e24
  let p158 : t93 = e25 := Eq.trans p157 p47
  let p159 : t93 = e49 := Eq.trans p158 p156
  let p160 : t94 = t95 := congrFun p90 e24
  let p161 : e50 = t95 := rfl
  let p163 : t95 = e50 := Eq.symm p161
  let p164 : t94 = e50 := Eq.trans p160 p163
  let p166 : t96 = t97 := congr p128 p164
  let p167 : e51 = t97 := rfl
  let p169 : t97 = e51 := Eq.symm p167
  let p170 : t96 = e51 := Eq.trans p166 p169
  let p172 : t93 = t96 := assoc e1 e0 e24
  let p173 : e49 = t93 := Eq.symm p159
  let p174 : e25 = t93 := Eq.trans p156 p173
  let p175 : e25 = t96 := Eq.trans p174 p172
  let p176 : e25 = e51 := Eq.trans p175 p170
  let p177 : e22 = e68 := comm e1 e2
  let p179 : e28 = e76 := comm e3 e4
  let p180 : e9 = e47 := Eq.trans p0 p155
  let p181 : t43 = e47 := Eq.trans p18 p180
  let p182 : t45 = t129 := congrArg e5 p181
  let p183 : t47 = t129 := congrArg e5 p180
  let p184 : e10 = t129 := Eq.trans p21 p183
  let p185 : t129 = e10 := Eq.symm p184
  let p186 : t45 = e10 := Eq.trans p182 p185
  let p188 : t130 = t131 := congrFun p186 e76
  let p189 : e23 = e9 := Eq.symm p0
  let p190 : e26 = e10 := congrArg e5 p189
  let p191 : e29 = t132 := rfl
  let p192 : t132 = t131 := congr p190 p179
  let p193 : e29 = t131 := Eq.trans p191 p192
  let p194 : t131 = e29 := Eq.symm p193
  let p195 : t130 = e29 := Eq.trans p188 p194
  let p197 : t133 = t134 := congrFun p36 e76
  let p198 : e52 = t135 := rfl
  let p199 : t135 = t134 := congrArg e16 p179
  let p200 : e52 = t134 := Eq.trans p198 p199
  let p201 : t134 = e52 := Eq.symm p200
  let p202 : t133 = e52 := Eq.trans p197 p201
  let p204 : t136 = t137 := congr p11 p202
  let p205 : e53 = t137 := rfl
  let p207 : t137 = e53 := Eq.symm p205
  let p208 : t136 = e53 := Eq.trans p204 p207
  let p210 : t130 = t136 := assoc e15 e2 e76
  let p211 : e29 = t130 := Eq.symm p195
  let p212 : e29 = t136 := Eq.trans p211 p210
  let p213 : e29 = e53 := Eq.trans p212 p208
  let p214 : e17 = e47 := Eq.trans p63 p155
  let p215 : t57 = e47 := Eq.trans p58 p214
  let p216 : t59 = t129 := congrArg e5 p215
  let p217 : t59 = e10 := Eq.trans p216 p185
  let p218 : t138 = t131 := congrFun p217 e76
  let p219 : t138 = e29 := Eq.trans p218 p194
  let p220 : t138 = e53 := Eq.trans p219 p213
  let p221 : t139 = t140 := congrFun p11 e76
  let p222 : e56 = t141 := rfl
  let p223 : t141 = t140 := congrArg e8 p179
  let p224 : e56 = t140 := Eq.trans p222 p223
  let p225 : t140 = e56 := Eq.symm p224
  let p226 : t139 = e56 := Eq.trans p221 p225
  let p228 : t142 = t143 := congr p36 p226
  let p229 : e57 = t143 := rfl
  let p231 : t143 = e57 := Eq.symm p229
  let p232 : t142 = e57 := Eq.trans p228 p231
  let p234 : t138 = t142 := assoc e2 e15 e76
  let p235 : e53 = t138 := Eq.symm p220
  let p236 : e29 = t138 := Eq.trans p213 p235
  let p237 : e29 = t142 := Eq.trans p236 p234
  let p238 : e29 = e57 := Eq.trans p237 p232
  let p240 : t144 = t145 := congrFun p90 e68
  let p241 : t70 = t145 := congrArg e6 p177
  let p242 : e23 = t145 := Eq.trans p94 p241
  let p243 : t145 = e23 := Eq.symm p242
  let p244 : t144 = e23 := Eq.trans p240 p243
  let p245 : t144 = e47 := Eq.trans p244 p155
  let p246 : t146 = t129 := congrArg e5 p245
  let p247 : t146 = e10 := Eq.trans p246 p185
  let p248 : t147 = t131 := congrFun p247 e76
  let p249 : t147 = e29 := Eq.trans p248 p194
  let p250 : t147 = e57 := Eq.trans p249 p238
  let p252 : t73 = t148 := congrArg e5 p177
  let p253 : e43 = t148 := Eq.trans p105 p252
  let p254 : t148 = e43 := Eq.symm p253
  let p255 : t149 = t150 := congrFun p254 e76
  let p256 : e58 = t151 := rfl
  let p257 : t151 = t150 := congrArg e43 p179
  let p258 : e58 = t150 := Eq.trans p256 p257
  let p259 : t150 = e58 := Eq.symm p258
  let p260 : t149 = e58 := Eq.trans p255 p259
  let p262 : t152 = t153 := congr p90 p260
  let p263 : e59 = t153 := rfl
  let p265 : t153 = e59 := Eq.symm p263
  let p266 : t152 = e59 := Eq.trans p262 p265
  let p268 : t147 = t152 := assoc e0 e68 e76
  let p269 : e57 = t147 := Eq.symm p250
  let p270 : e29 = t147 := Eq.trans p238 p269
  let p271 : e29 = t152 := Eq.trans p270 p268
  let p272 : e29 = e59 := Eq.trans p271 p266
  let p273 : t157 = t88 := congrFun p128 e46
  let p274 : t157 = e47 := Eq.trans p273 p149
  let p275 : t158 = t129 := congrArg e5 p274
  let p276 : t158 = e10 := Eq.trans p275 p185
  let p277 : t159 = t131 := congrFun p276 e76
  let p278 : t159 = e29 := Eq.trans p277 p194
  let p279 : t159 = e59 := Eq.trans p278 p272
  let p281 : e83 = t160 := rfl
  let p282 : t160 = e83 := Eq.symm p281
  let p284 : t161 = t162 := congrFun p282 e76
  let p285 : e84 = t162 := rfl
  let p287 : t162 = e84 := Eq.symm p285
  let p288 : t161 = e84 := Eq.trans p284 p287
  let p290 : t163 = t164 := congr p128 p288
  let p291 : e85 = t164 := rfl
  let p293 : t164 = e85 := Eq.symm p291
  let p294 : t163 = e85 := Eq.trans p290 p293
  let p296 : t159 = t163 := assoc e1 e46 e76
  let p297 : e59 = t159 := Eq.symm p279
  let p298 : e29 = t159 := Eq.trans p272 p297
  let p299 : e29 = t163 := Eq.trans p298 p296
  let p300 : e29 = e85 := Eq.trans p299 p294
  let p302 : t165 = t49 := congrFun p185 e3
  let p303 : t165 = e11 := Eq.trans p302 p31
  let p304 : e11 = e51 := Eq.trans p53 p176
  let p305 : t165 = e51 := Eq.trans p303 p304
  let p306 : t166 = t167 := congrArg e5 p305
  let p307 : e12 = t168 := rfl
  let p308 : t168 = t167 := congrArg e5 p304
  let p309 : e12 = t167 := Eq.trans p307 p308
  let p310 : t167 = e12 := Eq.symm p309
  let p311 : t166 = e12 := Eq.trans p306 p310
  let p314 : t169 = t170 := congrFun p311 e4
  let p315 : e13 = t170 := rfl
  let p317 : t170 = e13 := Eq.symm p315
  let p318 : t169 = e13 := Eq.trans p314 p317
  let p319 : t169 = e35 := Eq.trans p318 p2
  let p321 : e18 = t171 := rfl
  let p322 : t171 = e18 := Eq.symm p321
  let p324 : t172 = t173 := congrFun p322 e4
  let p325 : e28 = t173 := rfl
  let p327 : t173 = e28 := Eq.symm p325
  let p328 : t172 = e28 := Eq.trans p324 p327
  let p329 : t172 = e76 := Eq.trans p328 p179
  let p330 : t174 = t131 := congr p185 p329
  let p331 : t174 = e29 := Eq.trans p330 p194
  let p332 : t174 = e85 := Eq.trans p331 p300
  let p333 : t169 = t174 := assoc e47 e3 e4
  let p335 : e35 = t169 := Eq.symm p319
  let p336 : e35 = t174 := Eq.trans p335 p333
  let p337 : e35 = e85 := Eq.trans p336 p332
  let p349 : e13 = e85 := Eq.trans p2 p337
  let p503 : t231 = t232 := congrFun p322 e47
  let p504 : e19 = t233 := rfl
  let p505 : t233 = t232 := congrArg e18 p214
  let p506 : e19 = t232 := Eq.trans p504 p505
  let p507 : t232 = e19 := Eq.symm p506
  let p508 : t231 = e19 := Eq.trans p503 p507
  let p510 : t234 = t235 := congrArg e5 p508
  let p511 : e39 = t235 := rfl
  let p513 : t235 = e39 := Eq.symm p511
  let p514 : t234 = e39 := Eq.trans p510 p513
  let p516 : t236 = t237 := congrFun p514 e4
  let p517 : e40 = t237 := rfl
  let p519 : t237 = e40 := Eq.symm p517
  let p520 : t236 = e40 := Eq.trans p516 p519
  let p522 : t238 = t239 := congrFun p185 e4
  let p523 : e47 = e23 := Eq.symm p155
  let p524 : e47 = e9 := Eq.trans p523 p189
  let p525 : e54 = e10 := congrArg e5 p524
  let p526 : e63 = t240 := rfl
  let p527 : t240 = t239 := congrFun p525 e4
  let p528 : e63 = t239 := Eq.trans p526 p527
  let p529 : t239 = e63 := Eq.symm p528
  let p530 : t238 = e63 := Eq.trans p522 p529
  let p532 : t241 = t242 := congr p322 p530
  let p533 : e64 = t242 := rfl
  let p535 : t242 = e64 := Eq.symm p533
  let p536 : t241 = e64 := Eq.trans p532 p535
  let p538 : t236 = t241 := assoc e3 e47 e4
  let p539 : e40 = t236 := Eq.symm p520
  let p540 : e40 = t241 := Eq.trans p539 p538
  let p541 : e40 = e64 := Eq.trans p540 p536
  let p643 : e53 = e110 := assoc e0 e1 e52
  let p644 : t279 = t137 := congrFun p136 e52
  let p645 : t279 = e53 := Eq.trans p644 p207
  let p646 : t279 = e110 := Eq.trans p645 p643
  let p647 : t280 = t281 := congrFun p90 e52
  let p648 : e111 = t281 := rfl
  let p650 : t281 = e111 := Eq.symm p648
  let p651 : t280 = e111 := Eq.trans p647 p650
  let p653 : t282 = t283 := congr p128 p651
  let p654 : e112 = t283 := rfl
  let p656 : t283 = e112 := Eq.symm p654
  let p657 : t282 = e112 := Eq.trans p653 p656
  let p659 : t279 = t282 := assoc e1 e0 e52
  let p660 : e110 = t279 := Eq.symm p646
  let p661 : e53 = t279 := Eq.trans p643 p660
  let p662 : e53 = t282 := Eq.trans p661 p659
  let p663 : e53 = e112 := Eq.trans p662 p657
  let p865 : t356 = t357 := congrArg e5 p329
  let p866 : e77 = t357 := rfl
  let p868 : t357 = e77 := Eq.symm p866
  let p869 : t356 = e77 := Eq.trans p865 p868
  let p871 : t358 = t359 := congrFun p869 e47
  let p872 : e78 = t359 := rfl
  let p874 : t359 = e78 := Eq.symm p872
  let p875 : t358 = e78 := Eq.trans p871 p874
  let p878 : e20 = t360 := rfl
  let p879 : t360 = e20 := Eq.symm p878
  let p881 : t361 = t362 := congrFun p879 e47
  let p882 : e130 = t362 := rfl
  let p884 : t362 = e130 := Eq.symm p882
  let p885 : t361 = e130 := Eq.trans p881 p884
  let p887 : t363 = t364 := congr p322 p885
  let p888 : e131 = t364 := rfl
  let p890 : t364 = e131 := Eq.symm p888
  let p891 : t363 = e131 := Eq.trans p887 p890
  let p893 : t358 = t363 := assoc e3 e4 e47
  let p894 : e78 = t358 := Eq.symm p875
  let p895 : e78 = t363 := Eq.trans p894 p893
  let p896 : e78 = e131 := Eq.trans p895 p891
  let p897 : t365 = t366 := congrFun p879 e3
  let p898 : e76 = t366 := rfl
  let p900 : t366 = e76 := Eq.symm p898
  let p901 : t365 = e76 := Eq.trans p897 p900
  let p902 : t367 = t357 := congrArg e5 p901
  let p903 : t367 = e77 := Eq.trans p902 p868
  let p904 : t368 = t359 := congrFun p903 e47
  let p905 : t368 = e78 := Eq.trans p904 p874
  let p906 : t368 = e131 := Eq.trans p905 p896
  let p907 : t369 = t370 := congr p879 p508
  let p908 : e21 = t370 := rfl
  let p910 : t370 = e21 := Eq.symm p908
  let p911 : t369 = e21 := Eq.trans p907 p910
  let p912 : e21 = e64 := Eq.trans p4 p541
  let p913 : t369 = e64 := Eq.trans p911 p912
  let p914 : t368 = t369 := assoc e4 e3 e47
  let p915 : e131 = t368 := Eq.symm p906
  let p916 : e78 = t368 := Eq.trans p896 p915
  let p917 : e78 = t369 := Eq.trans p916 p914
  let p918 : e78 = e64 := Eq.trans p917 p913
  let p925 : t371 = t131 := congrFun p185 e76
  let p926 : t371 = e29 := Eq.trans p925 p194
  let p927 : e29 = e112 := Eq.trans p213 p663
  let p928 : t371 = e112 := Eq.trans p926 p927
  let p929 : t372 = t359 := congrFun p868 e47
  let p930 : t372 = e78 := Eq.trans p929 p874
  let p931 : t372 = e64 := Eq.trans p930 p918
  let p932 : t371 = t372 := comm e47 e76
  let p933 : e112 = t371 := Eq.symm p928
  let p934 : e29 = t371 := Eq.trans p927 p933
  let p935 : e29 = t372 := Eq.trans p934 p932
  let p936 : e29 = e64 := Eq.trans p935 p931
  let p1082 : e85 = e29 := Eq.symm p300
  let p1083 : e13 = e29 := Eq.trans p349 p1082
  let p1084 : e13 = e64 := Eq.trans p1083 p936
  let p4872 : e64 = e40 := Eq.symm p541
  let p4873 : e13 = e40 := Eq.trans p1084 p4872
  let p4874 : e40 = e21 := Eq.symm p4
  let p4875 : e13 = e21 := Eq.trans p4873 p4874
  exact p4875
