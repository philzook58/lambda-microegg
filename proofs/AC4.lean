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
  let t106 := e4 e1
  let t107 := t106 e0
  let t108 := e11 e0
  let t109 := e4 t107
  let t110 := e4 e12
  let t111 := e4 e6
  let t112 := t109 e19
  let t113 := e7 e19
  let t114 := e4 e0
  let t115 := t114 e19
  let t116 := e5 e19
  let t117 := t106 t115
  let t118 := e11 e35
  let t119 := t106 e26
  let t120 := e11 e26
  let t121 := e4 t119
  let t122 := e4 e27
  let t123 := t109 e2
  let t124 := e7 e2
  let t125 := t114 e2
  let t126 := e5 e2
  let t127 := t106 t125
  let t128 := e4 e8
  let t129 := t121 e3
  let t130 := e9 e3
  let t131 := t114 e39
  let t132 := e5 e39
  let t133 := e5 e17
  let t134 := e4 t131
  let t135 := t134 e3
  let t136 := e4 e2
  let t137 := t136 e12
  let t138 := e13 e12
  let t139 := e4 t137
  let t140 := t139 e3
  let t141 := t110 e3
  let t142 := e7 e3
  let t143 := t109 e3
  let t144 := t114 e3
  let t145 := e5 e3
  let t146 := t106 t144
  let t147 := e11 e48
  let t148 := t136 t141
  let t149 := e13 e49
  let t150 := e4 e39
  let t151 := e4 e17
  let t152 := t150 e3
  let t153 := e30 e3
  let t154 := t136 e1
  let t155 := e13 e1
  let t156 := e4 t154
  let t157 := t156 e3
  let t158 := t106 e3
  let t159 := e11 e3
  let t160 := t136 t158
  let t161 := e13 e46
  let t162 := t114 t152
  let t163 := e5 e50
  let t164 := e4 e26
  let t165 := t164 e3
  let t166 := e53 e3
  let t167 := t106 t165
  let t168 := e11 e54
  let t169 := e4 e3
  let t170 := t169 e27
  let t171 := e15 e27
  let t172 := e15 e14
  let t173 := t122 e3
  let p0 : e10 = e20 := assoc e6 e2 e3
  let p4 : e11 = t106 := rfl
  let p5 : t106 = e11 := Eq.symm p4
  let p8 : t107 = t108 := congrFun p5 e0
  let p9 : e12 = t108 := rfl
  let p11 : t108 = e12 := Eq.symm p9
  let p12 : t107 = e12 := Eq.trans p8 p11
  let p14 : t109 = t110 := congrArg e4 p12
  let p15 : e6 = e12 := comm e0 e1
  let p16 : e7 = t111 := rfl
  let p17 : t111 = t110 := congrArg e4 p15
  let p18 : e7 = t110 := Eq.trans p16 p17
  let p19 : t110 = e7 := Eq.symm p18
  let p20 : t109 = e7 := Eq.trans p14 p19
  let p23 : t112 = t113 := congrFun p20 e19
  let p24 : e20 = t113 := rfl
  let p26 : t113 = e20 := Eq.symm p24
  let p27 : t112 = e20 := Eq.trans p23 p26
  let p28 : e20 = e34 := assoc e0 e1 e19
  let p29 : t112 = e34 := Eq.trans p27 p28
  let p31 : e5 = t114 := rfl
  let p32 : t114 = e5 := Eq.symm p31
  let p34 : t115 = t116 := congrFun p32 e19
  let p35 : e35 = t116 := rfl
  let p37 : t116 = e35 := Eq.symm p35
  let p38 : t115 = e35 := Eq.trans p34 p37
  let p40 : t117 = t118 := congr p5 p38
  let p41 : e36 = t118 := rfl
  let p43 : t118 = e36 := Eq.symm p41
  let p44 : t117 = e36 := Eq.trans p40 p43
  let p46 : e34 = t112 := Eq.symm p29
  let p47 : e20 = t112 := Eq.trans p28 p46
  let p48 : t112 = t117 := assoc e1 e0 e19
  let p49 : e20 = t117 := Eq.trans p47 p48
  let p50 : e20 = e36 := Eq.trans p49 p44
  let p51 : e10 = e36 := Eq.trans p0 p50
  let p53 : t119 = t120 := congrFun p5 e26
  let p54 : e27 = t120 := rfl
  let p56 : t120 = e27 := Eq.symm p54
  let p57 : t119 = e27 := Eq.trans p53 p56
  let p59 : t121 = t122 := congrArg e4 p57
  let p60 : e8 = e18 := assoc e0 e1 e2
  let p62 : t123 = t124 := congrFun p20 e2
  let p63 : e8 = t124 := rfl
  let p65 : t124 = e8 := Eq.symm p63
  let p66 : t123 = e8 := Eq.trans p62 p65
  let p67 : t123 = e18 := Eq.trans p66 p60
  let p68 : t125 = t126 := congrFun p32 e2
  let p69 : e26 = t126 := rfl
  let p71 : t126 = e26 := Eq.symm p69
  let p72 : t125 = e26 := Eq.trans p68 p71
  let p73 : t127 = t120 := congr p5 p72
  let p74 : t127 = e27 := Eq.trans p73 p56
  let p76 : e18 = t123 := Eq.symm p67
  let p77 : t123 = t127 := assoc e1 e0 e2
  let p78 : e18 = t127 := Eq.trans p76 p77
  let p79 : e18 = e27 := Eq.trans p78 p74
  let p80 : e8 = e27 := Eq.trans p60 p79
  let p81 : e9 = t128 := rfl
  let p82 : t128 = t122 := congrArg e4 p80
  let p83 : e9 = t122 := Eq.trans p81 p82
  let p84 : t122 = e9 := Eq.symm p83
  let p85 : t121 = e9 := Eq.trans p59 p84
  let p88 : t129 = t130 := congrFun p85 e3
  let p89 : e10 = t130 := rfl
  let p91 : t130 = e10 := Eq.symm p89
  let p92 : t129 = e10 := Eq.trans p88 p91
  let p94 : t131 = t132 := congrFun p32 e39
  let p95 : e17 = e39 := comm e1 e2
  let p96 : e18 = t133 := rfl
  let p97 : t133 = t132 := congrArg e5 p95
  let p98 : e18 = t132 := Eq.trans p96 p97
  let p99 : t132 = e18 := Eq.symm p98
  let p100 : t131 = e18 := Eq.trans p94 p99
  let p101 : t131 = e27 := Eq.trans p100 p79
  let p102 : t134 = t122 := congrArg e4 p101
  let p103 : t134 = e9 := Eq.trans p102 p84
  let p104 : t135 = t130 := congrFun p103 e3
  let p105 : t135 = e10 := Eq.trans p104 p91
  let p107 : e13 = t136 := rfl
  let p108 : t136 = e13 := Eq.symm p107
  let p110 : t137 = t138 := congrFun p108 e12
  let p111 : e14 = t138 := rfl
  let p113 : t138 = e14 := Eq.symm p111
  let p114 : t137 = e14 := Eq.trans p110 p113
  let p115 : e14 = e23 := comm e2 e12
  let p116 : e12 = e6 := Eq.symm p15
  let p117 : e22 = e7 := congrArg e4 p116
  let p118 : e23 = e8 := congrFun p117 e2
  let p119 : e14 = e8 := Eq.trans p115 p118
  let p120 : e14 = e18 := Eq.trans p119 p60
  let p121 : e14 = e27 := Eq.trans p120 p79
  let p122 : t137 = e27 := Eq.trans p114 p121
  let p123 : t139 = t122 := congrArg e4 p122
  let p124 : t139 = e9 := Eq.trans p123 p84
  let p125 : t140 = t130 := congrFun p124 e3
  let p126 : t140 = e10 := Eq.trans p125 p91
  let p127 : t140 = e36 := Eq.trans p126 p51
  let p129 : t141 = t142 := congrFun p19 e3
  let p130 : e28 = t142 := rfl
  let p132 : t142 = e28 := Eq.symm p130
  let p133 : t141 = e28 := Eq.trans p129 p132
  let p134 : t143 = t142 := congrFun p20 e3
  let p135 : t143 = e28 := Eq.trans p134 p132
  let p136 : e28 = e47 := assoc e0 e1 e3
  let p137 : t143 = e47 := Eq.trans p135 p136
  let p138 : t144 = t145 := congrFun p32 e3
  let p139 : e48 = t145 := rfl
  let p141 : t145 = e48 := Eq.symm p139
  let p142 : t144 = e48 := Eq.trans p138 p141
  let p144 : t146 = t147 := congr p5 p142
  let p145 : e49 = t147 := rfl
  let p147 : t147 = e49 := Eq.symm p145
  let p148 : t146 = e49 := Eq.trans p144 p147
  let p150 : e47 = t143 := Eq.symm p137
  let p151 : e28 = t143 := Eq.trans p136 p150
  let p152 : t143 = t146 := assoc e1 e0 e3
  let p153 : e28 = t146 := Eq.trans p151 p152
  let p154 : e28 = e49 := Eq.trans p153 p148
  let p155 : t141 = e49 := Eq.trans p133 p154
  let p156 : t148 = t149 := congr p108 p155
  let p157 : e51 = t149 := rfl
  let p159 : t149 = e51 := Eq.symm p157
  let p160 : t148 = e51 := Eq.trans p156 p159
  let p162 : e36 = t140 := Eq.symm p127
  let p163 : t140 = t148 := assoc e2 e12 e3
  let p164 : e36 = t148 := Eq.trans p162 p163
  let p165 : e36 = e51 := Eq.trans p164 p160
  let p166 : e10 = e51 := Eq.trans p51 p165
  let p167 : t135 = e51 := Eq.trans p105 p166
  let p169 : e30 = t151 := rfl
  let p170 : t151 = t150 := congrArg e4 p95
  let p171 : e30 = t150 := Eq.trans p169 p170
  let p172 : t150 = e30 := Eq.symm p171
  let p174 : t152 = t153 := congrFun p172 e3
  let p175 : e31 = t153 := rfl
  let p177 : t153 = e31 := Eq.symm p175
  let p178 : t152 = e31 := Eq.trans p174 p177
  let p179 : t154 = t155 := congrFun p108 e1
  let p180 : e39 = t155 := rfl
  let p182 : t155 = e39 := Eq.symm p180
  let p183 : t154 = e39 := Eq.trans p179 p182
  let p184 : t156 = t150 := congrArg e4 p183
  let p185 : t156 = e30 := Eq.trans p184 p172
  let p186 : t157 = t153 := congrFun p185 e3
  let p187 : t157 = e31 := Eq.trans p186 p177
  let p188 : e31 = e33 := assoc e1 e2 e3
  let p189 : t157 = e33 := Eq.trans p187 p188
  let p190 : t158 = t159 := congrFun p5 e3
  let p191 : e46 = t159 := rfl
  let p193 : t159 = e46 := Eq.symm p191
  let p194 : t158 = e46 := Eq.trans p190 p193
  let p196 : t160 = t161 := congr p108 p194
  let p197 : e50 = t161 := rfl
  let p199 : t161 = e50 := Eq.symm p197
  let p200 : t160 = e50 := Eq.trans p196 p199
  let p202 : e33 = t157 := Eq.symm p189
  let p203 : e31 = t157 := Eq.trans p188 p202
  let p204 : t157 = t160 := assoc e2 e1 e3
  let p205 : e31 = t160 := Eq.trans p203 p204
  let p206 : e31 = e50 := Eq.trans p205 p200
  let p207 : t152 = e50 := Eq.trans p178 p206
  let p208 : t162 = t163 := congr p32 p207
  let p209 : e52 = t163 := rfl
  let p211 : t163 = e52 := Eq.symm p209
  let p212 : t162 = e52 := Eq.trans p208 p211
  let p214 : e51 = t135 := Eq.symm p167
  let p215 : e36 = t135 := Eq.trans p165 p214
  let p216 : t135 = t162 := assoc e0 e39 e3
  let p217 : e36 = t162 := Eq.trans p215 p216
  let p218 : e36 = e52 := Eq.trans p217 p212
  let p219 : e10 = e52 := Eq.trans p51 p218
  let p220 : t129 = e52 := Eq.trans p92 p219
  let p222 : e53 = t164 := rfl
  let p223 : t164 = e53 := Eq.symm p222
  let p225 : t165 = t166 := congrFun p223 e3
  let p226 : e54 = t166 := rfl
  let p228 : t166 = e54 := Eq.symm p226
  let p229 : t165 = e54 := Eq.trans p225 p228
  let p231 : t167 = t168 := congr p5 p229
  let p232 : e55 = t168 := rfl
  let p234 : t168 = e55 := Eq.symm p232
  let p235 : t167 = e55 := Eq.trans p231 p234
  let p237 : e52 = t129 := Eq.symm p220
  let p238 : e36 = t129 := Eq.trans p218 p237
  let p239 : t129 = t167 := assoc e1 e26 e3
  let p240 : e36 = t167 := Eq.trans p238 p239
  let p241 : e36 = e55 := Eq.trans p240 p235
  let p242 : e10 = e55 := Eq.trans p51 p241
  let p244 : e15 = t169 := rfl
  let p245 : t169 = e15 := Eq.symm p244
  let p247 : t170 = t171 := congrFun p245 e27
  let p248 : e16 = t172 := rfl
  let p249 : t172 = t171 := congrArg e15 p121
  let p250 : e16 = t171 := Eq.trans p248 p249
  let p251 : t171 = e16 := Eq.symm p250
  let p252 : t170 = e16 := Eq.trans p247 p251
  let p255 : t173 = t130 := congrFun p84 e3
  let p256 : t173 = e10 := Eq.trans p255 p91
  let p257 : t173 = e55 := Eq.trans p256 p242
  let p258 : e16 = t170 := Eq.symm p252
  let p259 : t170 = t173 := comm e3 e27
  let p260 : e16 = t173 := Eq.trans p258 p259
  let p261 : e16 = e55 := Eq.trans p260 p257
  let p262 : e55 = e16 := Eq.symm p261
  let p263 : e10 = e16 := Eq.trans p242 p262
  exact p263
