(echo "A leading @ makes an operator bind the following name.")

(insert
  (@sum i
    (@sum j
      (@sum k
        (* (a i j) (a j k))))))

; ?c is bare beneath k, so it may use i and j but cannot use k.
; {?f k} may use k. Include both product orientations.
(rewrite
  (@sum k (* {?f k} ?c))
  (* ?c (@sum k {?f k})))
(rewrite
  (@sum k (* ?c {?f k}))
  (* ?c (@sum k {?f k})))

(run 10)

(match
  (@sum i (@sum j (* {?c i j} (@sum k {?f j k})))))

(guard
  (@sum i (@sum j (@sum k (* (a i j) (a j k)))))
  (@sum i (@sum j (* (a i j) (@sum k (a j k))))))

(extract
  (@sum i (@sum j (* (a i j) (@sum k (a j k))))))
