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
  let t465 := e5 e3
  let t466 := t465 e41
  let t467 := e18 e41
  let t468 := e5 e1
  let t469 := t468 e0
  let t470 := e14 e0
  let t471 := e5 t469
  let t472 := e5 e15
  let t473 := e5 e7
  let t474 := t471 e2
  let t475 := e8 e2
  let t476 := e5 e0
  let t477 := t476 e2
  let t478 := e6 e2
  let t479 := t468 t477
  let t480 := e14 e40
  let t481 := e18 e17
  let t482 := e5 e41
  let t483 := e5 e9
  let t484 := t482 e3
  let t485 := e10 e3
  let t486 := t471 e24
  let t487 := e8 e24
  let t488 := t476 e24
  let t489 := e6 e24
  let t490 := t468 t488
  let t491 := e14 e49
  let t492 := t468 e40
  let t493 := e5 t492
  let t494 := t493 e3
  let t495 := t476 e62
  let t496 := e6 e62
  let t497 := e6 e22
  let t498 := e5 t495
  let t499 := t498 e3
  let t500 := e5 e2
  let t501 := t500 e15
  let t502 := e16 e15
  let t503 := e5 t501
  let t504 := t503 e3
  let t505 := t472 e3
  let t506 := e8 e3
  let t507 := t471 e3
  let t508 := t476 e3
  let t509 := e6 e3
  let t510 := t468 t508
  let t511 := e14 e78
  let t512 := t500 t505
  let t513 := e16 e79
  let t514 := e5 e62
  let t515 := e5 e22
  let t516 := t514 e3
  let t517 := e44 e3
  let t518 := t500 e1
  let t519 := e16 e1
  let t520 := e5 t518
  let t521 := t520 e3
  let t522 := t468 e3
  let t523 := e14 e3
  let t524 := t500 t522
  let t525 := e16 e76
  let t526 := t476 t516
  let t527 := e6 e80
  let t528 := e5 e40
  let t529 := t528 e3
  let t530 := e83 e3
  let t531 := t468 t529
  let t532 := e14 e84
  let p3 : e18 = t465 := rfl
  let p4 : t465 = e18 := Eq.symm p3
  let p7 : t466 = t467 := congrFun p4 e41
  let p8 : e17 = e32 := comm e2 e15
  let p9 : e7 = e15 := comm e0 e1
  let p10 : e15 = e7 := Eq.symm p9
  let p11 : e31 = e8 := congrArg e5 p10
  let p13 : e32 = e9 := congrFun p11 e2
  let p14 : e17 = e9 := Eq.trans p8 p13
  let p15 : e9 = e23 := assoc e0 e1 e2
  let p16 : e17 = e23 := Eq.trans p14 p15
  let p19 : e14 = t468 := rfl
  let p20 : t468 = e14 := Eq.symm p19
  let p23 : t469 = t470 := congrFun p20 e0
  let p24 : e15 = t470 := rfl
  let p26 : t470 = e15 := Eq.symm p24
  let p27 : t469 = e15 := Eq.trans p23 p26
  let p29 : t471 = t472 := congrArg e5 p27
  let p30 : e8 = t473 := rfl
  let p31 : t473 = t472 := congrArg e5 p9
  let p32 : e8 = t472 := Eq.trans p30 p31
  let p33 : t472 = e8 := Eq.symm p32
  let p34 : t471 = e8 := Eq.trans p29 p33
  let p36 : t474 = t475 := congrFun p34 e2
  let p37 : e9 = t475 := rfl
  let p39 : t475 = e9 := Eq.symm p37
  let p40 : t474 = e9 := Eq.trans p36 p39
  let p41 : t474 = e23 := Eq.trans p40 p15
  let p43 : e6 = t476 := rfl
  let p44 : t476 = e6 := Eq.symm p43
  let p46 : t477 = t478 := congrFun p44 e2
  let p47 : e40 = t478 := rfl
  let p49 : t478 = e40 := Eq.symm p47
  let p50 : t477 = e40 := Eq.trans p46 p49
  let p52 : t479 = t480 := congr p20 p50
  let p53 : e41 = t480 := rfl
  let p55 : t480 = e41 := Eq.symm p53
  let p56 : t479 = e41 := Eq.trans p52 p55
  let p58 : e23 = t474 := Eq.symm p41
  let p59 : t474 = t479 := assoc e1 e0 e2
  let p60 : e23 = t479 := Eq.trans p58 p59
  let p61 : e23 = e41 := Eq.trans p60 p56
  let p62 : e17 = e41 := Eq.trans p16 p61
  let p63 : e19 = t481 := rfl
  let p64 : t481 = t467 := congrArg e18 p62
  let p65 : e19 = t467 := Eq.trans p63 p64
  let p66 : t467 = e19 := Eq.symm p65
  let p67 : t466 = e19 := Eq.trans p7 p66
  let p70 : e9 = e41 := Eq.trans p15 p61
  let p71 : e10 = t483 := rfl
  let p72 : t483 = t482 := congrArg e5 p70
  let p73 : e10 = t482 := Eq.trans p71 p72
  let p74 : t482 = e10 := Eq.symm p73
  let p76 : t484 = t485 := congrFun p74 e3
  let p77 : e11 = t485 := rfl
  let p79 : t485 = e11 := Eq.symm p77
  let p80 : t484 = e11 := Eq.trans p76 p79
  let p81 : e11 = e25 := assoc e7 e2 e3
  let p83 : t486 = t487 := congrFun p34 e24
  let p84 : e25 = t487 := rfl
  let p86 : t487 = e25 := Eq.symm p84
  let p87 : t486 = e25 := Eq.trans p83 p86
  let p88 : e25 = e48 := assoc e0 e1 e24
  let p89 : t486 = e48 := Eq.trans p87 p88
  let p90 : t488 = t489 := congrFun p44 e24
  let p91 : e49 = t489 := rfl
  let p93 : t489 = e49 := Eq.symm p91
  let p94 : t488 = e49 := Eq.trans p90 p93
  let p96 : t490 = t491 := congr p20 p94
  let p97 : e50 = t491 := rfl
  let p99 : t491 = e50 := Eq.symm p97
  let p100 : t490 = e50 := Eq.trans p96 p99
  let p102 : e48 = t486 := Eq.symm p89
  let p103 : e25 = t486 := Eq.trans p88 p102
  let p104 : t486 = t490 := assoc e1 e0 e24
  let p105 : e25 = t490 := Eq.trans p103 p104
  let p106 : e25 = e50 := Eq.trans p105 p100
  let p107 : e11 = e50 := Eq.trans p81 p106
  let p108 : t492 = t480 := congrFun p20 e40
  let p109 : t492 = e41 := Eq.trans p108 p55
  let p110 : t493 = t482 := congrArg e5 p109
  let p111 : t493 = e10 := Eq.trans p110 p74
  let p112 : t494 = t485 := congrFun p111 e3
  let p113 : t494 = e11 := Eq.trans p112 p79
  let p115 : t495 = t496 := congrFun p44 e62
  let p116 : e22 = e62 := comm e1 e2
  let p117 : e23 = t497 := rfl
  let p118 : t497 = t496 := congrArg e6 p116
  let p119 : e23 = t496 := Eq.trans p117 p118
  let p120 : t496 = e23 := Eq.symm p119
  let p121 : t495 = e23 := Eq.trans p115 p120
  let p122 : t495 = e41 := Eq.trans p121 p61
  let p123 : t498 = t482 := congrArg e5 p122
  let p124 : t498 = e10 := Eq.trans p123 p74
  let p125 : t499 = t485 := congrFun p124 e3
  let p126 : t499 = e11 := Eq.trans p125 p79
  let p128 : e16 = t500 := rfl
  let p129 : t500 = e16 := Eq.symm p128
  let p131 : t501 = t502 := congrFun p129 e15
  let p132 : e17 = t502 := rfl
  let p134 : t502 = e17 := Eq.symm p132
  let p135 : t501 = e17 := Eq.trans p131 p134
  let p136 : t501 = e41 := Eq.trans p135 p62
  let p137 : t503 = t482 := congrArg e5 p136
  let p138 : t503 = e10 := Eq.trans p137 p74
  let p139 : t504 = t485 := congrFun p138 e3
  let p140 : t504 = e11 := Eq.trans p139 p79
  let p141 : t504 = e50 := Eq.trans p140 p107
  let p143 : t505 = t506 := congrFun p33 e3
  let p144 : e42 = t506 := rfl
  let p146 : t506 = e42 := Eq.symm p144
  let p147 : t505 = e42 := Eq.trans p143 p146
  let p148 : t507 = t506 := congrFun p34 e3
  let p149 : t507 = e42 := Eq.trans p148 p146
  let p150 : e42 = e77 := assoc e0 e1 e3
  let p151 : t507 = e77 := Eq.trans p149 p150
  let p152 : t508 = t509 := congrFun p44 e3
  let p153 : e78 = t509 := rfl
  let p155 : t509 = e78 := Eq.symm p153
  let p156 : t508 = e78 := Eq.trans p152 p155
  let p158 : t510 = t511 := congr p20 p156
  let p159 : e79 = t511 := rfl
  let p161 : t511 = e79 := Eq.symm p159
  let p162 : t510 = e79 := Eq.trans p158 p161
  let p164 : e77 = t507 := Eq.symm p151
  let p165 : e42 = t507 := Eq.trans p150 p164
  let p166 : t507 = t510 := assoc e1 e0 e3
  let p167 : e42 = t510 := Eq.trans p165 p166
  let p168 : e42 = e79 := Eq.trans p167 p162
  let p169 : t505 = e79 := Eq.trans p147 p168
  let p170 : t512 = t513 := congr p129 p169
  let p171 : e81 = t513 := rfl
  let p173 : t513 = e81 := Eq.symm p171
  let p174 : t512 = e81 := Eq.trans p170 p173
  let p176 : e50 = t504 := Eq.symm p141
  let p177 : t504 = t512 := assoc e2 e15 e3
  let p178 : e50 = t512 := Eq.trans p176 p177
  let p179 : e50 = e81 := Eq.trans p178 p174
  let p180 : e11 = e81 := Eq.trans p107 p179
  let p181 : t499 = e81 := Eq.trans p126 p180
  let p183 : e44 = t515 := rfl
  let p184 : t515 = t514 := congrArg e5 p116
  let p185 : e44 = t514 := Eq.trans p183 p184
  let p186 : t514 = e44 := Eq.symm p185
  let p188 : t516 = t517 := congrFun p186 e3
  let p189 : e45 = t517 := rfl
  let p191 : t517 = e45 := Eq.symm p189
  let p192 : t516 = e45 := Eq.trans p188 p191
  let p193 : t518 = t519 := congrFun p129 e1
  let p194 : e62 = t519 := rfl
  let p196 : t519 = e62 := Eq.symm p194
  let p197 : t518 = e62 := Eq.trans p193 p196
  let p198 : t520 = t514 := congrArg e5 p197
  let p199 : t520 = e44 := Eq.trans p198 p186
  let p200 : t521 = t517 := congrFun p199 e3
  let p201 : t521 = e45 := Eq.trans p200 p191
  let p202 : e45 = e47 := assoc e1 e2 e3
  let p203 : t521 = e47 := Eq.trans p201 p202
  let p204 : t522 = t523 := congrFun p20 e3
  let p205 : e76 = t523 := rfl
  let p207 : t523 = e76 := Eq.symm p205
  let p208 : t522 = e76 := Eq.trans p204 p207
  let p210 : t524 = t525 := congr p129 p208
  let p211 : e80 = t525 := rfl
  let p213 : t525 = e80 := Eq.symm p211
  let p214 : t524 = e80 := Eq.trans p210 p213
  let p216 : e47 = t521 := Eq.symm p203
  let p217 : e45 = t521 := Eq.trans p202 p216
  let p218 : t521 = t524 := assoc e2 e1 e3
  let p219 : e45 = t524 := Eq.trans p217 p218
  let p220 : e45 = e80 := Eq.trans p219 p214
  let p221 : t516 = e80 := Eq.trans p192 p220
  let p222 : t526 = t527 := congr p44 p221
  let p223 : e82 = t527 := rfl
  let p225 : t527 = e82 := Eq.symm p223
  let p226 : t526 = e82 := Eq.trans p222 p225
  let p228 : e81 = t499 := Eq.symm p181
  let p229 : e50 = t499 := Eq.trans p179 p228
  let p230 : t499 = t526 := assoc e0 e62 e3
  let p231 : e50 = t526 := Eq.trans p229 p230
  let p232 : e50 = e82 := Eq.trans p231 p226
  let p233 : e11 = e82 := Eq.trans p107 p232
  let p234 : t494 = e82 := Eq.trans p113 p233
  let p236 : e83 = t528 := rfl
  let p237 : t528 = e83 := Eq.symm p236
  let p239 : t529 = t530 := congrFun p237 e3
  let p240 : e84 = t530 := rfl
  let p242 : t530 = e84 := Eq.symm p240
  let p243 : t529 = e84 := Eq.trans p239 p242
  let p245 : t531 = t532 := congr p20 p243
  let p246 : e85 = t532 := rfl
  let p248 : t532 = e85 := Eq.symm p246
  let p249 : t531 = e85 := Eq.trans p245 p248
  let p251 : e82 = t494 := Eq.symm p234
  let p252 : e50 = t494 := Eq.trans p232 p251
  let p253 : t494 = t531 := assoc e1 e40 e3
  let p254 : e50 = t531 := Eq.trans p252 p253
  let p255 : e50 = e85 := Eq.trans p254 p249
  let p256 : e11 = e85 := Eq.trans p107 p255
  let p257 : t484 = e85 := Eq.trans p80 p256
  let p258 : e19 = t466 := Eq.symm p67
  let p259 : t466 = t484 := comm e3 e41
  let p260 : e19 = t484 := Eq.trans p258 p259
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
