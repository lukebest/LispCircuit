#lang racket
;; Pass 1: explicit widths, no implicit casts, match completeness,
;; static index checks. Errors accumulate as diag values.

(require "diag.rkt" "types.rkt" "ast.rkt" "nhir.rkt")
(provide check-module check-algos)

(struct bind (ty kind rename) #:transparent)

(define current-prefix (make-parameter "v"))
(define current-state-names (make-parameter (set)))
(define current-enums (make-parameter (hash)))
(define used-names (make-parameter (set)))

(define (fresh! base)
  (let loop ([n 0])
    (define s (if (zero? n) (string->symbol base)
                  (string->symbol (format "~a_~a" base n))))
    (if (set-member? (used-names) s)
        (loop (add1 n))
        (begin (used-names (set-add (used-names) s)) s))))

(define (mark! s)
  (used-names (set-add (used-names) s)))

(define (emit info code msg
              #:expected [expected #f]
              #:actual [actual #f]
              #:suggestion [suggestion ""])
  (diag-add! (diag-at code info
                      #:message msg
                      #:expected expected
                      #:actual actual
                      #:suggestion suggestion)))

(define (lit-min-type v)
  (cond
    [(negative? v)
     (let loop ([w 1])
       (if (fits-lit? v (ty-sint w)) (ty-sint w) (loop (add1 w))))]
    [else
     (let loop ([w 1])
       (if (fits-lit? v (ty-uint w)) (ty-uint w) (loop (add1 w))))]))

(define (resize-suggestion expected actual)
  (define ew (ty-width expected))
  (define aw (ty-width actual))
  (cond
    [(and (ty-sint? expected) (ty-sint? actual) (< aw ew))
     (format "Wrap expression with (sext <expr> ~a)" ew)]
    [(and (ty-uint? expected) (ty-uint? actual) (< aw ew))
     (format "Wrap expression with (zext <expr> ~a)" ew)]
    [(< aw ew)
     (format "Resize with (~a <expr> ~a)" (if (ty-sint? expected) "sext" "zext") ew)]
    [(> aw ew)
     (format "Wrap expression with (trunc <expr> ~a)" ew)]
    [else ""]))

(define (emit-mismatch expected actual info)
  (define et (if (string? expected) #f expected))
  (define at (if (string? actual) #f actual))
  (define es (if (string? expected) expected (ty->string expected)))
  (define as (if (string? actual) actual (ty->string actual)))
  (define sign?
    (and et at
         (or (and (ty-uint? et) (ty-sint? at))
             (and (ty-sint? et) (ty-uint? at)))))
  (define width?
    (and et at
         (ty-scalar? et) (ty-scalar? at)
         (not (ty-enum? et)) (not (ty-enum? at))
         (eq? (ty-kind et) (ty-kind at))
         (not (= (ty-width et) (ty-width at)))))
  (cond
    [sign?
     (emit info "ERR_SIGN_MISMATCH" "signedness does not match"
           #:expected es #:actual as
           #:suggestion "Use (as-uint ...) or (as-sint ...) to reinterpret, then resize")]
    [width?
     (emit info "ERR_WIDTH_MISMATCH" "bit width does not match"
           #:expected es #:actual as
           #:suggestion (resize-suggestion et at))]
    [else
     (emit info "ERR_TYPE_MISMATCH" "type does not match"
           #:expected es #:actual as
           #:suggestion "Make the expression's type match the context")]))

(define (ensure e expected)
  (define t (expr-ty e))
  (define info (expr-info e))
  (cond
    ;; #f expected means "infer". #f as an expression type is untyped.
    [(or (not t) (ty-err? t)) e]
    [(not expected) e]
    [(ty-err? expected) (e-bad (ty-err) info)]
    [(unsized? t)
     (if (and (e-lit? e) (fits-lit? (e-lit-val e) expected))
         (e-lit (e-lit-val e) expected (e-lit-info e))
         (begin
           (emit-mismatch expected (if (e-lit? e) (lit-min-type (e-lit-val e)) t) info)
           (e-bad (ty-err) info)))]
    [(ty=? t expected) e]
    [else
     (emit-mismatch expected t info)
     (e-bad (ty-err) info)]))

(define (enum-hits name)
  (filter (lambda (en) (memq name (ty-enum-variants en)))
          (hash-values (current-enums))))

(define (variant-lit name en info)
  (e-lit (index-of (ty-enum-variants en) name) en info))

(define (resolve-ref name info expected env)
  (cond
    [(hash-ref env name #f)
     => (lambda (b)
          (ensure (e-ref (or (bind-rename b) name) (bind-ty b) info) expected))]
    [(set-member? (current-state-names) name)
     (emit info "ERR_ALGO_STATEFUL"
           (format "defalgo cannot refer to state or table ~a" name)
           #:suggestion "Pass the value as a defalgo parameter; algos must be pure")
     (e-bad (ty-err) info)]
    [(and expected (ty-enum? expected) (memq name (ty-enum-variants expected)))
     (ensure (variant-lit name expected info) expected)]
    [else
     (define hits (enum-hits name))
     (cond
       [(= (length hits) 1)
        (ensure (variant-lit name (car hits) info) expected)]
       [(> (length hits) 1)
        (emit info "ERR_PARSE" (format "variant ~a is ambiguous" name)
              #:suggestion "Qualify it as Enum.VARIANT")]
       [else
        (emit info "ERR_UNDEFINED" (format "undefined name ~a" name)
              #:suggestion (format "Define ~a before use" name))])
     (e-bad (ty-err) info)]))

(define (both-bad? a b)
  (or (bad-ty? (expr-ty a)) (bad-ty? (expr-ty b))))

(define (unify-same a0 b0 op expected env info)
  (define a1 (check-expr a0 #f env))
  (define b1 (check-expr b0 #f env))
  (cond
    [(both-bad? a1 b1) (e-bad (ty-err) info)]
    [(and (unsized? (expr-ty a1)) (unsized? (expr-ty b1)))
     (cond
       [expected
        (define a2 (check-expr a0 expected env))
        (define b2 (check-expr b0 expected env))
        (if (both-bad? a2 b2)
            (e-bad (ty-err) info)
            (ensure (e-binop op a2 b2 expected info) expected))]
       [(and (e-lit? a1) (e-lit? b1) (memq op '(+ - * & \| ^)))
        (e-lit (fold-lit op (e-lit-val a1) (e-lit-val b1)) (ty-int) info)]
       [else
        (emit info "ERR_AMBIGUOUS_WIDTH" (format "cannot infer the width of ~a" op)
              #:suggestion "Give an operand a concrete type with (u W v) or (s W v)")
        (e-bad (ty-err) info)])]
    [(unsized? (expr-ty a1))
     (define a2 (ensure a1 (expr-ty b1)))
     (finish-same op a2 b1 info expected)]
    [(unsized? (expr-ty b1))
     (define b2 (ensure b1 (expr-ty a1)))
     (finish-same op a1 b2 info expected)]
    [(ty=? (expr-ty a1) (expr-ty b1))
     (finish-same op a1 b1 info expected)]
    [else
     (emit-mismatch (expr-ty a1) (expr-ty b1) info)
     (e-bad (ty-err) info)]))

(define (finish-same op a b info expected)
  (define t (expr-ty a))
  (cond
    [(bad-ty? t) (e-bad (ty-err) info)]
    [(not (or (ty-uint? t) (ty-sint? t) (and (ty-enum? t) (memq op '(== !=)))))
     (cond
       [(memq op '(== != < <= > >=))
        (if (and (ty=? (expr-ty a) (expr-ty b)) (or (ty-enum? t) (ty-uint? t) (ty-sint? t)))
            (ensure (e-binop op a b (ty-uint 1) info) expected)
            (begin
              (emit info "ERR_TYPE_MISMATCH" (format "~a requires scalar operands" op)
                    #:actual (ty->string t))
              (e-bad (ty-err) info)))]
       [else
        (emit info "ERR_TYPE_MISMATCH" (format "~a requires a uint or sint" op)
              #:actual (ty->string t))
        (e-bad (ty-err) info)])]
    [(memq op '(== != < <= > >=))
     (ensure (e-binop op a b (ty-uint 1) info) expected)]
    [else
     (ensure (e-binop op a b t info) expected)]))

(define (fold-lit op x y)
  (case op
    [(+) (+ x y)]
    [(-) (- x y)]
    [(*) (* x y)]
    [(&) (bitwise-and x y)]
    [(\|) (bitwise-ior x y)]
    [(^) (bitwise-xor x y)]
    [else 0]))

(define (check-cmp op a0 b0 expected env info)
  (define a1 (check-expr a0 #f env))
  (define hint (let ([t (expr-ty a1)]) (if (or (ty-enum? t) (ty-uint? t) (ty-sint? t)) t #f)))
  (define b1 (check-expr b0 hint env))
  (define a2
    (if (and (unsized? (expr-ty a1)) (not (unsized? (expr-ty b1))) (not (bad-ty? (expr-ty b1))))
        (ensure a1 (expr-ty b1))
        a1))
  (define b2
    (if (and (unsized? (expr-ty b1)) (not (unsized? (expr-ty a2))) (not (bad-ty? (expr-ty a2))))
        (ensure b1 (expr-ty a2))
        b1))
  (cond
    [(both-bad? a2 b2) (e-bad (ty-err) info)]
    [(not (ty=? (expr-ty a2) (expr-ty b2)))
     (emit-mismatch (expr-ty a2) (expr-ty b2) info)
     (e-bad (ty-err) info)]
    [else (ensure (e-binop op a2 b2 (ty-uint 1) info) expected)]))

(define (check-wide op a0 b0 expected env info)
  ;; +w / -w : result width is max+1. *w handled separately.
  (define want
    (match expected
      [(ty-uint w) #:when (>= w 2) (ty-uint (sub1 w))]
      [(ty-sint w) #:when (>= w 2) (ty-sint (sub1 w))]
      [_ #f]))
  (define a1 (check-expr a0 #f env))
  (define b1 (check-expr b0 (if (unsized? (expr-ty a1)) want (expr-ty a1)) env))
  (define a2
    (cond
      [(bad-ty? (expr-ty b1)) a1]
      [(unsized? (expr-ty a1)) (ensure a1 (expr-ty b1))]
      [else a1]))
  (define b2
    (if (and (not (bad-ty? (expr-ty a2))) (unsized? (expr-ty b1)))
        (ensure b1 (expr-ty a2))
        b1))
  (cond
    [(both-bad? a2 b2) (e-bad (ty-err) info)]
    [(not (ty=? (expr-ty a2) (expr-ty b2)))
     (emit-mismatch (expr-ty a2) (expr-ty b2) info)
     (e-bad (ty-err) info)]
    [(not (or (ty-uint? (expr-ty a2)) (ty-sint? (expr-ty a2))))
     (emit info "ERR_TYPE_MISMATCH" (format "~a requires uint or sint" op)
           #:actual (ty->string (expr-ty a2)))
     (e-bad (ty-err) info)]
    [else
     (define rt (if (ty-sint? (expr-ty a2))
                    (ty-sint (add1 (ty-width (expr-ty a2))))
                    (ty-uint (add1 (ty-width (expr-ty a2))))))
     (ensure (e-binop op a2 b2 rt info) expected)]))

(define (check-mulw a0 b0 expected env info)
  (define a1 (check-expr a0 #f env))
  (define b1 (check-expr b0 #f env))
  (cond
    [(both-bad? a1 b1) (e-bad (ty-err) info)]
    [(or (unsized? (expr-ty a1)) (unsized? (expr-ty b1)))
     (emit info "ERR_AMBIGUOUS_WIDTH" "cannot infer *w operand widths"
           #:suggestion "Give both operands a concrete uint or sint type")
     (e-bad (ty-err) info)]
    [(or (and (ty-uint? (expr-ty a1)) (ty-sint? (expr-ty b1)))
         (and (ty-sint? (expr-ty a1)) (ty-uint? (expr-ty b1))))
     (emit-mismatch (expr-ty a1) (expr-ty b1) info)
     (e-bad (ty-err) info)]
    [(not (and (or (ty-uint? (expr-ty a1)) (ty-sint? (expr-ty a1)))
               (or (ty-uint? (expr-ty b1)) (ty-sint? (expr-ty b1)))))
     (emit info "ERR_TYPE_MISMATCH" "*w requires uint or sint operands")
     (e-bad (ty-err) info)]
    [else
     (define signed? (or (ty-sint? (expr-ty a1)) (ty-sint? (expr-ty b1))))
     (define w (+ (ty-width (expr-ty a1)) (ty-width (expr-ty b1))))
     (define rt (if signed? (ty-sint w) (ty-uint w)))
     (ensure (e-binop '*w a1 b1 rt info) expected)]))

(define (check-shift op a0 b0 expected env info)
  (define a1 (check-expr a0 expected env))
  (define b1 (check-expr b0 #f env))
  (define b2
    (cond
      [(bad-ty? (expr-ty b1)) b1]
      [(unsized? (expr-ty b1))
       (ensure b1 (lit-min-type (if (e-lit? b1) (max 0 (e-lit-val b1)) 1)))]
      [(ty-uint? (expr-ty b1)) b1]
      [else
       (emit info "ERR_SIGN_MISMATCH" "shift amount must be unsigned"
             #:expected "(uint ?)" #:actual (ty->string (expr-ty b1))
             #:suggestion "Use (as-uint ...) if the bit pattern is the shift count")
       (e-bad (ty-err) info)]))
  (cond
    [(or (bad-ty? (expr-ty a1)) (bad-ty? (expr-ty b2))) (e-bad (ty-err) info)]
    [(not (or (ty-uint? (expr-ty a1)) (ty-sint? (expr-ty a1))))
     (emit info "ERR_TYPE_MISMATCH" "shift requires a uint or sint value"
           #:actual (ty->string (expr-ty a1)))
     (e-bad (ty-err) info)]
    [else (ensure (e-binop op a1 b2 (expr-ty a1) info) expected)]))

(define (check-expr e expected env)
  (define info (expr-info e))
  (match e
    [(e-bad _ _) e]
    [(e-lit v t i)
     (if (unsized? t)
         (if expected (ensure e expected) e)
         (ensure e expected))]
    [(e-ref name _ i) (resolve-ref name i expected env)]
    [(e-child inst port _ i)
     (define h (ainst-mod (hash-ref (current-insts) inst)))
     (define p (hmod-port h port))
     (cond
       [p (ensure (e-child inst port (hport-ty p) i) expected)]
       [(hmod-alias h port)
        (emit i "ERR_TYPE_MISMATCH"
              (format "~a.~a is a stream; use valid, ready, or bits" inst port)
              #:suggestion (format "Write (valid ~a.~a), (ready ~a.~a), or (bits ~a.~a)"
                                   inst port inst port inst port))
        (e-bad (ty-err) i)]
       [else
        (emit i "ERR_UNDEFINED" (format "unknown port ~a.~a" inst port))
        (e-bad (ty-err) i)])]
    [(e-binop op a b _ i)
     (case op
       [(+ - * & \| ^) (unify-same a b op expected env i)]
       [(and or)
        (define a1 (check-expr a (ty-uint 1) env))
        (define b1 (check-expr b (ty-uint 1) env))
        (if (or (bad-ty? (expr-ty a1)) (bad-ty? (expr-ty b1)))
            (e-bad (ty-err) i)
            (ensure (e-binop op a1 b1 (ty-uint 1) i) expected))]
       [(== != < <= > >=) (check-cmp op a b expected env i)]
       [(+w -w) (check-wide op a b expected env i)]
       [(*w) (check-mulw a b expected env i)]
       [(<< >>) (check-shift op a b expected env i)]
       [else
        (emit i "ERR_PARSE" (format "unknown operator ~a" op))
        (e-bad (ty-err) i)])]
    [(e-unop op a _ i)
     (case op
       [(not)
        (define a1 (check-expr a (ty-uint 1) env))
        (if (bad-ty? (expr-ty a1))
            (e-bad (ty-err) i)
            (ensure (e-unop 'not a1 (ty-uint 1) i) expected))]
       [(~ -)
        (define a1 (check-expr a expected env))
        (define t (expr-ty a1))
        (cond
          [(bad-ty? t) (e-bad (ty-err) i)]
          [(not (or (ty-uint? t) (ty-sint? t)))
           (emit i "ERR_TYPE_MISMATCH" (format "~a requires uint or sint" op)
                 #:actual (ty->string t))
           (e-bad (ty-err) i)]
          [else (ensure (e-unop op a1 t i) expected)])]
       [else (emit i "ERR_PARSE" "bad unary") (e-bad (ty-err) i)])]
    [(e-mux c t f _ i)
     (define c1 (check-expr c (ty-uint 1) env))
     (define t1 (check-expr t expected env))
     (define f-expect (if (or (unsized? (expr-ty t1)) (bad-ty? (expr-ty t1))) expected (expr-ty t1)))
     (define f1 (check-expr f f-expect env))
     (define t2
       (if (and (unsized? (expr-ty t1)) (not (bad-ty? (expr-ty f1))) (not (unsized? (expr-ty f1))))
           (check-expr t (expr-ty f1) env)
           t1))
     (cond
       [(or (bad-ty? (expr-ty c1)) (bad-ty? (expr-ty t2)) (bad-ty? (expr-ty f1)))
        (e-bad (ty-err) i)]
       [(not (ty=? (expr-ty t2) (expr-ty f1)))
        (emit-mismatch (expr-ty t2) (expr-ty f1) i)
        (e-bad (ty-err) i)]
       [else (ensure (e-mux c1 t2 f1 (expr-ty t2) i) expected)])]
    [(e-match sel cases default _ i) (check-match sel cases default expected env i)]
    [(e-field base fname _ i)
     (define b1 (check-expr base #f env))
     (define t (expr-ty b1))
     (cond
       [(bad-ty? t) (e-bad (ty-err) i)]
       [(not (ty-bundle? t))
        (emit i "ERR_TYPE_MISMATCH" "field access requires a bundle" #:actual (ty->string t))
        (e-bad (ty-err) i)]
       [else
        (define f (assoc fname (ty-bundle-fields t)))
        (cond
          [f (ensure (e-field b1 fname (cdr f) i) expected)]
          [else
           (emit i "ERR_UNDEFINED" (format "bundle has no field ~a" fname))
           (e-bad (ty-err) i)])])]
    [(e-idx base index _ i)
     (define b1 (check-expr base #f env))
     (define t (expr-ty b1))
     (cond
       [(bad-ty? t) (e-bad (ty-err) i)]
       [(not (ty-vec? t))
        (emit i "ERR_TYPE_MISMATCH" "idx requires a vec" #:actual (ty->string t))
        (e-bad (ty-err) i)]
       [else
        (define i1 (check-expr index #f env))
        (when (and (e-lit? i1) (or (< (e-lit-val i1) 0) (>= (e-lit-val i1) (ty-vec-n t))))
          (emit i "ERR_INDEX_OOB"
                (format "index ~a is outside [0, ~a)" (e-lit-val i1) (ty-vec-n t))
                #:suggestion (format "Index ~a is outside [0, ~a)" (e-lit-val i1) (ty-vec-n t)))
          ;; Keep going with a fitting index type so the out-of-range literal
          ;; does not also raise a width error.
          )
        (define i2
          (cond
            [(bad-ty? (expr-ty i1)) i1]
            [(unsized? (expr-ty i1))
             (define need (max 1 (integer-length (max 1 (abs (e-lit-val i1))))))
             (define aw (max need (max 1 (integer-length (max 1 (sub1 (ty-vec-n t)))))))
             (ensure i1 (ty-uint aw))]
            [(ty-uint? (expr-ty i1)) i1]
            [else
             (emit (expr-info i1) "ERR_SIGN_MISMATCH" "index must be unsigned"
                   #:expected "(uint ?)" #:actual (ty->string (expr-ty i1)))
             (e-bad (ty-err) (expr-info i1))]))
        (if (bad-ty? (expr-ty i2))
            (e-bad (ty-err) i)
            (ensure (e-idx b1 i2 (ty-vec-elem t) i) expected))])]
    [(e-cast kind a ty0 i)
     (define a1 (check-expr a #f env))
     (define at (expr-ty a1))
     (cond
       [(bad-ty? at) (e-bad (ty-err) i)]
       [(memq kind '(zext sext trunc))
        (define w (ty-uint-w ty0))
        (define aw (ty-width at))
        (cond
          [(not (or (ty-uint? at) (ty-sint? at) (ty-enum? at)))
           (emit i "ERR_TYPE_MISMATCH" "cast requires a scalar" #:actual (ty->string at))
           (e-bad (ty-err) i)]
          [(and (eq? kind 'trunc) (> w aw))
           (emit i "ERR_WIDTH_MISMATCH" "trunc width is wider than the value"
                 #:expected (format "~a" aw) #:actual (format "~a" w)
                 #:suggestion (format "Use (zext <expr> ~a) or (sext <expr> ~a)" w w))
           (e-bad (ty-err) i)]
          [(and (memq kind '(zext sext)) (< w aw))
           (emit i "ERR_WIDTH_MISMATCH" "extension width is narrower than the value"
                 #:suggestion (format "Wrap expression with (trunc <expr> ~a)" w))
           (e-bad (ty-err) i)]
          [else
           (define rt
             (case kind
               [(zext) (ty-uint w)]
               [(sext) (ty-sint w)]
               [(trunc) (if (ty-sint? at) (ty-sint w) (ty-uint w))]))
           (ensure (e-cast kind a1 rt i) expected)])]
       [(memq kind '(as-uint as-sint))
        (define w (ty-width at))
        (define rt (if (eq? kind 'as-uint) (ty-uint w) (ty-sint w)))
        (ensure (e-cast kind a1 rt i) expected)]
       [else (emit i "ERR_PARSE" "bad cast") (e-bad (ty-err) i)])]
    [(e-slice a hi lo t i)
     (define a1 (check-expr a #f env))
     (define at (expr-ty a1))
     (cond
       [(bad-ty? at) (e-bad (ty-err) i)]
       [(not (or (ty-uint? at) (ty-sint? at) (ty-enum? at)))
        (emit i "ERR_TYPE_MISMATCH" "bits slice requires a scalar" #:actual (ty->string at))
        (e-bad (ty-err) i)]
       [(>= hi (ty-width at))
        (emit i "ERR_INDEX_OOB" (format "bit ~a is outside a ~a-bit value" hi (ty-width at))
              #:suggestion (format "Index ~a is outside [0, ~a)" hi (ty-width at)))
        (e-bad (ty-err) i)]
       [else (ensure (e-slice a1 hi lo t i) expected)])]
    [(e-cat ps _ i)
     (define ps1 (map (lambda (p) (check-expr p #f env)) ps))
     (cond
       [(ormap (lambda (p) (bad-ty? (expr-ty p))) ps1) (e-bad (ty-err) i)]
       [(ormap (lambda (p) (unsized? (expr-ty p))) ps1)
        (emit i "ERR_AMBIGUOUS_WIDTH" "cat cannot size an unsized literal"
              #:suggestion "Write literals as (u W value)")
        (e-bad (ty-err) i)]
       [(ormap (lambda (p) (not (or (ty-uint? (expr-ty p)) (ty-sint? (expr-ty p)) (ty-enum? (expr-ty p))))) ps1)
        (emit i "ERR_TYPE_MISMATCH" "cat requires scalar parts")
        (e-bad (ty-err) i)]
       [else
        (define w (apply + (map (lambda (p) (ty-width (expr-ty p))) ps1)))
        (ensure (e-cat ps1 (ty-uint w) i) expected)])]
    [(e-pack fields _ i)
     (define exp-fields (and (ty-bundle? expected) (ty-bundle-fields expected)))
     (define fs
       (for/list ([f fields])
         (define et (and exp-fields (assoc (car f) exp-fields)))
         (cons (car f) (check-expr (cdr f) (and et (cdr et)) env))))
     (cond
       [(ormap (lambda (f) (or (bad-ty? (expr-ty (cdr f))) (unsized? (expr-ty (cdr f))))) fs)
        (emit i "ERR_AMBIGUOUS_WIDTH" "pack field needs a concrete type")
        (e-bad (ty-err) i)]
       [else
        (define ty (ty-bundle (map (lambda (f) (cons (car f) (expr-ty (cdr f)))) fs)))
        (when exp-fields
          (unless (= (length exp-fields) (length fs))
            (emit i "ERR_TYPE_MISMATCH" "pack fields do not match the expected bundle"
                  #:expected (ty->string expected) #:actual (ty->string ty))))
        (ensure (e-pack fs ty i) expected)])]
    [(e-vlit ps _ i)
     (cond
       [(ty-vec? expected)
        (unless (= (length ps) (ty-vec-n expected))
          (emit i "ERR_TYPE_MISMATCH"
                (format "vlit has ~a elements, expected ~a" (length ps) (ty-vec-n expected))))
        (define ps1 (map (lambda (p) (check-expr p (ty-vec-elem expected) env)) ps))
        (if (ormap (lambda (p) (bad-ty? (expr-ty p))) ps1)
            (e-bad (ty-err) i)
            (ensure (e-vlit ps1 expected i) expected))]
       [else
        (define ps1 (map (lambda (p) (check-expr p #f env)) ps))
        (cond
          [(or (null? ps1) (ormap (lambda (p) (or (bad-ty? (expr-ty p)) (unsized? (expr-ty p)))) ps1))
           (emit i "ERR_AMBIGUOUS_WIDTH" "vlit needs concrete element types")
           (e-bad (ty-err) i)]
          [(not (andmap (lambda (p) (ty=? (expr-ty p) (expr-ty (car ps1)))) ps1))
           (emit i "ERR_TYPE_MISMATCH" "vlit elements must share one type")
           (e-bad (ty-err) i)]
          [else
           (define ty (ty-vec (length ps1) (expr-ty (car ps1))))
           (ensure (e-vlit ps1 ty i) expected)])])]
    [(e-tread name addr _ i)
     (define tbl (hash-ref (current-tables) name #f))
     (cond
       [(not tbl)
        (emit i "ERR_UNDEFINED" (format "unknown table ~a" name))
        (e-bad (ty-err) i)]
       [(= (atable-latency tbl) 1)
        (emit i "ERR_PARSE" (format "table ~a has latency 1; read data with (table-rdata ~a)" name name)
              #:suggestion "Issue (table-read tbl addr) as a statement and use (table-rdata tbl) next cycle")
        (e-bad (ty-err) i)]
       [else
        (define aw (max 1 (integer-length (max 1 (sub1 (atable-depth tbl))))))
        (define a1 (check-expr addr #f env))
        (define a2
          (cond
            [(bad-ty? (expr-ty a1)) a1]
            [(unsized? (expr-ty a1)) (ensure a1 (ty-uint aw))]
            [(ty-uint? (expr-ty a1)) a1]
            [else
             (emit i "ERR_SIGN_MISMATCH" "table address must be unsigned"
                   #:actual (ty->string (expr-ty a1)))
             (e-bad (ty-err) i)]))
        (when (and (e-lit? a2) (or (< (e-lit-val a2) 0) (>= (e-lit-val a2) (atable-depth tbl))))
          (emit i "ERR_INDEX_OOB"
                (format "address ~a is outside [0, ~a)" (e-lit-val a2) (atable-depth tbl))
                #:suggestion (format "Index ~a is outside [0, ~a)" (e-lit-val a2) (atable-depth tbl))))
        (if (bad-ty? (expr-ty a2))
            (e-bad (ty-err) i)
            (ensure (e-tread name a2 (atable-elem-ty tbl) i) expected))])]
    [(e-rdata name _ i)
     (define tbl (hash-ref (current-tables) name #f))
     (cond
       [(not tbl)
        (emit i "ERR_UNDEFINED" (format "unknown table ~a" name))
        (e-bad (ty-err) i)]
       [(= (atable-latency tbl) 0)
        (emit i "ERR_PARSE" (format "table ~a is latency 0; use (table-read ~a addr)" name name))
        (e-bad (ty-err) i)]
       [else (ensure (e-rdata name (atable-elem-ty tbl) i) expected)])]
    [(e-call name args _ i)
     (define algo (hash-ref (current-algos) name #f))
     (cond
       [(not algo)
        (emit i "ERR_UNDEFINED" (format "unknown algorithm or operator ~a" name)
              #:suggestion "Define it with defalgo, or use a built-in operator")
        (e-bad (ty-err) i)]
       [(not (= (length args) (length (aalgo-params algo))))
        (emit i "ERR_PARSE" (format "~a expects ~a arguments" name (length (aalgo-params algo))))
        (e-bad (ty-err) i)]
       [else
        (define args2
          (for/list ([a args] [p (aalgo-params algo)])
            (check-expr a (cdr p) env)))
        (if (ormap (lambda (a) (bad-ty? (expr-ty a))) args2)
            (e-bad (ty-err) i)
            (ensure (e-call name args2 (aalgo-ret algo) i) expected))])]
    [(e-let name expr body _ i)
     (define e1 (check-expr expr #f env))
     (define et (expr-ty e1))
     (cond
       [(bad-ty? et) (e-bad (ty-err) i)]
       [(unsized? et)
        (emit (expr-info e1) "ERR_AMBIGUOUS_WIDTH"
              (format "cannot infer the type of ~a" name)
              #:suggestion "Annotate the bound value, for example (u 8 1) or (s 8 -1)")
        (e-bad (ty-err) i)]
       [else
        (define fr (fresh! (format "~a__~a" (current-prefix) name)))
        (define env2 (hash-set env name (bind et 'let fr)))
        (define b2 (check-expr body expected env2))
        (if (bad-ty? (expr-ty b2))
            (e-bad (ty-err) i)
            (e-let fr e1 b2 (expr-ty b2) i))])]
    [(e-sget op _ _ i)
     (emit i "ERR_INTERNAL" (format "unresolved ~a" op))
     (e-bad (ty-err) i)]
    [_ (emit info "ERR_INTERNAL" "bad expression") (e-bad (ty-err) info)]))

(define (check-match sel cases default expected env info)
  (define s1 (check-expr sel #f env))
  (define st (expr-ty s1))
  (cond
    [(bad-ty? st) (e-bad (ty-err) info)]
    [(not default)
     (emit info "ERR_MATCH_NO_DEFAULT" "match is missing a :default clause"
           #:suggestion "Add a (:default <expr>) clause")
     (e-bad (ty-err) info)]
    [else
     (define d1 (check-expr default expected env))
     (define acc0
       (cond
         [(bad-ty? (expr-ty d1)) #f]
         [(unsized? (expr-ty d1))
          (emit (expr-info d1) "ERR_AMBIGUOUS_WIDTH" "cannot infer match result type"
                #:suggestion "Give :default a concrete type")
          #f]
         [else d1]))
     (define seen (mutable-set))
     (define mux
       (and acc0
            (for/fold ([acc acc0] [ok? #t] #:result (and ok? acc))
                      ([c (reverse cases)])
              (define pat (car c))
              (define pe (pattern-expr pat st info))
              (when (set-member? seen pat)
                (emit info "ERR_PARSE" (format "duplicate match pattern ~a" pat)))
              (set-add! seen pat)
              (if (or (not pe) (bad-ty? (expr-ty pe)))
                  (values acc #f)
                  (let ([b (check-expr (cdr c) (expr-ty acc) env)])
                    (if (bad-ty? (expr-ty b))
                        (values acc #f)
                        (values (e-mux (e-binop '== s1 pe (ty-uint 1) info)
                                       b acc (expr-ty acc) info)
                                #t)))))))
     (if (not mux)
         (e-bad (ty-err) info)
         (ensure mux expected))]))

(define (pattern-expr pat st info)
  (cond
    [(exact-integer? pat)
     (if (and (or (ty-uint? st) (ty-sint? st)) (fits-lit? pat st))
         (e-lit pat st info)
         (begin
           (emit info "ERR_TYPE_MISMATCH" (format "pattern ~a does not fit ~a" pat (ty->string st))
                 #:expected (ty->string st))
           #f))]
    [(symbol? pat)
     (cond
       [(and (ty-enum? st) (memq pat (ty-enum-variants st)))
        (variant-lit pat st info)]
       [else
        (emit info "ERR_PARSE" (format "pattern ~a does not match ~a" pat (ty->string st))
              #:suggestion "Use an enum variant or :default")
        #f])]
    [else #f]))

(define current-insts (make-parameter (hash)))
(define current-tables (make-parameter (hash)))
(define current-algos (make-parameter (hash)))

(define (check-stmt st env seen)
  (match st
    [(st-set reg expr info)
     (define b (hash-ref env reg #f))
     (cond
       [(not (and b (eq? (bind-kind b) 'reg)))
        (emit info "ERR_UNDEFINED" (format "set! target ~a is not a register" reg)
              #:suggestion "set! only writes :state registers")
        (values (st-set reg (e-bad (ty-err) info) info) seen)]
       [(set-member? seen reg)
        (emit info "ERR_PARSE" (format "register ~a is assigned twice in one rule" reg)
              #:suggestion "Combine the updates into a single set!")
        (values (st-set reg (check-expr expr (bind-ty b) env) info) seen)]
       [else
        (values (st-set reg (check-expr expr (bind-ty b) env) info)
                (set-add seen reg))])]
    [(st-twrite tbl addr data info)
     (define t (hash-ref (current-tables) tbl #f))
     (define key (string->symbol (format "write:~a" tbl)))
     (cond
       [(not t)
        (emit info "ERR_UNDEFINED" (format "unknown table ~a" tbl))
        (values st seen)]
       [(set-member? seen key)
        (emit info "ERR_PARSE" (format "table ~a is written twice in one rule" tbl))
        (values st seen)]
       [else
        (define aw (max 1 (integer-length (max 1 (sub1 (atable-depth t))))))
        (define a1 (check-addr addr aw info env))
        (define d1 (check-expr data (atable-elem-ty t) env))
        (values (st-twrite tbl a1 d1 info) (set-add seen key))])]
    [(st-tread tbl addr info)
     (define t (hash-ref (current-tables) tbl #f))
     (define key (string->symbol (format "read:~a" tbl)))
     (cond
       [(not t)
        (emit info "ERR_UNDEFINED" (format "unknown table ~a" tbl))
        (values st seen)]
       [(= (atable-latency t) 0)
        (emit info "ERR_PARSE" "latency-0 table-read is an expression, not a statement"
              #:suggestion "Use (table-read tbl addr) inside a wire or assign")
        (values st seen)]
       [(set-member? seen key)
        (emit info "ERR_PARSE" (format "table ~a is read twice in one rule" tbl))
        (values st seen)]
       [else
        (define aw (max 1 (integer-length (max 1 (sub1 (atable-depth t))))))
        (values (st-tread tbl (check-addr addr aw info env) info) (set-add seen key))])]
    [(st-drive inst port expr info)
     (unless (eq? (amod-kind (current-module)) 'system)
       (emit info "ERR_PARSE" "drive is only allowed inside defsystem"))
     (define ins (hash-ref (current-insts) inst #f))
     (define p (and ins (hmod-port (ainst-mod ins) port)))
     (cond
       [(not p)
        (emit info "ERR_UNDEFINED" (format "unknown port ~a.~a" inst port))
        (values st seen)]
       [(not (eq? (hport-dir p) 'in))
        (emit info "ERR_PARSE" (format "~a.~a is an output and cannot be driven" inst port))
        (values st seen)]
       [else
        (define key (string->symbol (format "drive:~a.~a" inst port)))
        (when (set-member? seen key)
          (emit info "ERR_PARSE" (format "~a.~a is driven twice in one rule" inst port)))
        (values (st-drive inst port (check-expr expr (hport-ty p) env) info)
                (set-add seen key))])]
    [(st-log level parts info)
     (define parts2
       (map (lambda (p)
              (if (eq? (car p) 'val)
                  (list 'val (concretize (check-expr (cadr p) #f env)))
                  p))
            parts))
     (values (st-log level parts2 info) seen)]
    [(st-check expr msg info)
     (values (st-check (check-expr expr (ty-uint 1) env) msg info) seen)]
    [(st-finish info) (values st seen)]
    [(st-let bindings body info)
     (define-values (bs env2)
       (for/fold ([bs '()] [env env]) ([b bindings])
         (define e1 (concretize (check-expr (cadr b) #f env)))
         (define et (expr-ty e1))
         (define fr (fresh! (format "~a__~a" (current-prefix) (car b))))
         (define envn (hash-set env (car b) (bind (if (bad-ty? et) (ty-err) et) 'let fr)))
         (values (append bs (list (list fr e1))) envn)))
     (define-values (body2 seen2) (check-stmts body env2 seen))
     (values (st-let bs body2 info) seen2)]))

(define (concretize e)
  (if (and (e-lit? e) (unsized? (expr-ty e)))
      (e-lit (e-lit-val e) (lit-min-type (e-lit-val e)) (expr-info e))
      e))

(define (check-addr addr aw info env)
  (define a1 (check-expr addr #f env))
  (cond
    [(bad-ty? (expr-ty a1)) a1]
    [(unsized? (expr-ty a1)) (ensure a1 (ty-uint aw))]
    [(ty-uint? (expr-ty a1)) a1]
    [else
     (emit info "ERR_SIGN_MISMATCH" "address must be unsigned" #:actual (ty->string (expr-ty a1)))
     (e-bad (ty-err) info)]))

(define (check-stmts stmts env seen)
  (for/fold ([out '()] [seen seen]) ([st stmts])
    (define-values (st2 seen2) (check-stmt st env seen))
    (values (append out (list st2)) seen2)))

(define current-module (make-parameter #f))

(define (check-rule r env)
  (parameterize ([current-prefix (symbol->string (arule-name r))])
    (define g (check-expr (arule-guard r) (ty-uint 1) env))
    (define-values (body _) (check-stmts (arule-body r) env (set)))
    (struct-copy arule r [guard g] [body body])))

(define (check-algo algo)
  (define env
    (for/hash ([p (aalgo-params algo)])
      (values (car p) (bind (cdr p) 'param #f))))
  (parameterize ([current-prefix (format "algo_~a" (aalgo-name algo))])
    (define body (check-expr (aalgo-body algo) (aalgo-ret algo) env))
    (struct-copy aalgo algo [body body])))

(define (check-algos algos enums)
  (parameterize ([current-enums enums]
                 [current-state-names (set)]
                 [current-insts (hash)]
                 [current-tables (hash)]
                 [current-module #f]
                 [used-names (set)]
                 [current-algos (for/hash ([a algos]) (values (aalgo-name a) a))])
    (map check-algo algos)))

(define (check-module m enums algos)
  (parameterize ([current-enums enums]
                 [current-state-names
                  (set-union
                   (list->set (map areg-name (amod-regs m)))
                   (list->set (map atable-name (amod-tables m))))]
                 [current-insts (for/hash ([i (amod-insts m)]) (values (ainst-name i) i))]
                 [current-tables (for/hash ([t (amod-tables m)]) (values (atable-name t) t))]
                 [current-module m]
                 [used-names
                  (set-union
                   (list->set (map aport-name (amod-ports m)))
                   (list->set (map areg-name (amod-regs m)))
                   (list->set (map awire-name (amod-wires m)))
                   (list->set (map atable-name (amod-tables m)))
                   (list->set (map ainst-name (amod-insts m))))])
    (define local-algos
      (for/hash ([a (amod-algos m)]) (values (aalgo-name a) a)))
    (define all-algos (for/fold ([h algos]) ([(k v) (in-hash local-algos)]) (hash-set h k v)))
    (define checked-algos
      (parameterize ([current-algos all-algos])
        (map check-algo (amod-algos m))))
    (define algo-hash
      (for/fold ([h algos]) ([a checked-algos])
        (hash-set h (aalgo-name a) a)))
    (parameterize ([current-algos algo-hash])
      (define env (make-hash))
      (for ([p (amod-ports m)])
        (hash-set! env (aport-name p) (bind (aport-ty p) 'port #f)))
      (for ([r (amod-regs m)])
        (when (hash-has-key? env (areg-name r))
          (emit (areg-info r) "ERR_PARSE" (format "duplicate name ~a" (areg-name r))))
        (hash-set! env (areg-name r) (bind (areg-ty r) 'reg #f)))
      (for ([w (amod-wires m)])
        (define old (hash-ref env (awire-name w) #f))
        (when (and old (not (ty=? (bind-ty old) (awire-ty w))) (eq? (bind-kind old) 'port))
          (emit (awire-info w) "ERR_TYPE_MISMATCH"
                (format "wire ~a does not match port type" (awire-name w))
                #:expected (ty->string (bind-ty old))
                #:actual (ty->string (awire-ty w))))
        (when (and old (eq? (bind-kind old) 'reg))
          (emit (awire-info w) "ERR_PARSE" (format "wire ~a collides with a register" (awire-name w))))
        (hash-set! env (awire-name w) (bind (awire-ty w) 'wire #f)))
      (define env-i (make-immutable-hash (hash->list env)))
      (define wires
        (map (lambda (w)
               (struct-copy awire w [expr (check-expr (awire-expr w) (awire-ty w) env-i)]))
             (amod-wires m)))
      (define regs
        (map (lambda (r)
               (struct-copy areg r [init (check-expr (areg-init r) (areg-ty r) env-i)]))
             (amod-regs m)))
      (define rules (map (lambda (r) (check-rule r env-i)) (amod-rules m)))
      (define insts
        (for/list ([ins (amod-insts m)])
          (define cs
            (for/hash ([(k v) (in-hash (ainst-connects ins))])
              (define p (hmod-port (ainst-mod ins) k))
              (values k (check-expr v (hport-ty p) env-i))))
          (struct-copy ainst ins [connects cs])))
      (flush-diags!)
      (struct-copy amod m
                   [regs regs]
                   [wires wires]
                   [rules rules]
                   [algos checked-algos]
                   [insts insts]))))
