#lang racket
;; Core LCIR expressions, statements, and module structure.
;; Every node carries an info path so diagnostics can name it.

(require "diag.rkt" "types.rkt")
(provide (all-defined-out))

(struct e-ref (name ty info) #:transparent)
(struct e-child (inst port ty info) #:transparent)
(struct e-lit (val ty info) #:transparent)
(struct e-binop (op a b ty info) #:transparent)
(struct e-unop (op a ty info) #:transparent)
(struct e-mux (c t f ty info) #:transparent)
(struct e-field (base fname ty info) #:transparent)
(struct e-idx (base index ty info) #:transparent)
(struct e-cast (kind a ty info) #:transparent) ;; zext sext trunc as-uint as-sint
(struct e-slice (a hi lo ty info) #:transparent)
(struct e-cat (ps ty info) #:transparent)
(struct e-pack (fields ty info) #:transparent) ;; (listof (cons symbol expr))
(struct e-vlit (ps ty info) #:transparent)
(struct e-tread (tname addr ty info) #:transparent)
(struct e-rdata (tname ty info) #:transparent)
(struct e-call (name args ty info) #:transparent)
(struct e-let (name expr body ty info) #:transparent)
(struct e-sget (op arg ty info) #:transparent) ;; valid / ready / bits, eliminated by typecheck
(struct e-match (sel cases default ty info) #:transparent) ;; lowered by typecheck
(struct e-bad (ty info) #:transparent)

(struct st-set (reg expr info) #:transparent)
(struct st-twrite (tbl addr data info) #:transparent)
(struct st-tread (tbl addr info) #:transparent)
(struct st-drive (inst port expr info) #:transparent)
(struct st-log (level parts info) #:transparent)
(struct st-check (expr msg info) #:transparent)
(struct st-finish (info) #:transparent)
(struct st-let (bindings body info) #:transparent)

(struct arule (name prio guard body cf? info) #:transparent)
(struct awire (name ty expr info) #:transparent)
(struct areg (name ty init reset-less? clock info) #:transparent)
(struct atable (name depth elem-ty latency clock info) #:transparent)
(struct ainst (name mod connects info) #:transparent)
(struct aport (name dir ty info) #:transparent)
(struct salias (name elem dir valid ready bits) #:transparent)
(struct aalgo (name params ret body info) #:transparent)
(struct amod (name kind params clocks ports aliases regs tables insts wires rules algos info)
  #:transparent)

(define (expr? e)
  (or (e-ref? e) (e-child? e) (e-lit? e) (e-binop? e) (e-unop? e) (e-mux? e)
      (e-field? e) (e-idx? e) (e-cast? e) (e-slice? e) (e-cat? e) (e-pack? e)
      (e-vlit? e) (e-tread? e) (e-rdata? e) (e-call? e)       (e-let? e) (e-sget? e) (e-match? e)
      (e-bad? e)))

(define (expr-ty e)
  (match e
    [(e-ref _ t _) t]
    [(e-child _ _ t _) t]
    [(e-lit _ t _) t]
    [(e-binop _ _ _ t _) t]
    [(e-unop _ _ t _) t]
    [(e-mux _ _ _ t _) t]
    [(e-field _ _ t _) t]
    [(e-idx _ _ t _) t]
    [(e-cast _ _ t _) t]
    [(e-slice _ _ _ t _) t]
    [(e-cat _ t _) t]
    [(e-pack _ t _) t]
    [(e-vlit _ t _) t]
    [(e-tread _ _ t _) t]
    [(e-rdata _ t _) t]
    [(e-call _ _ t _) t]
    [(e-let _ _ _ t _) t]
    [(e-sget _ _ t _) t]
    [(e-match _ _ _ t _) t]
    [(e-bad t _) t]
    [_ (error 'expr-ty "not an expr: ~a" e)]))

(define (expr-info e)
  (match e
    [(or (e-ref _ _ i) (e-child _ _ _ i) (e-lit _ _ i) (e-binop _ _ _ _ i)
         (e-unop _ _ _ i) (e-mux _ _ _ _ i) (e-field _ _ _ i) (e-idx _ _ _ i)
         (e-cast _ _ _ i) (e-slice _ _ _ _ i) (e-cat _ _ i) (e-pack _ _ i)
         (e-vlit _ _ i) (e-tread _ _ _ i) (e-rdata _ _ i) (e-call _ _ _ i)
         (e-let _ _ _ _ i) (e-sget _ _ _ i) (e-match _ _ _ _ i) (e-bad _ i))
     i]
    [_ #f]))

(define (bad-ty? t)
  (or (not t) (ty-err? t)))

(define (expr-map-kids proc e)
  (define (k x) (proc x))
  (match e
    [(e-binop op a b t i) (e-binop op (k a) (k b) t i)]
    [(e-unop op a t i) (e-unop op (k a) t i)]
    [(e-mux c t f ty i) (e-mux (k c) (k t) (k f) ty i)]
    [(e-field b f ty i) (e-field (k b) f ty i)]
    [(e-idx b ix ty i) (e-idx (k b) (k ix) ty i)]
    [(e-cast kind a ty i) (e-cast kind (k a) ty i)]
    [(e-slice a hi lo ty i) (e-slice (k a) hi lo ty i)]
    [(e-cat ps ty i) (e-cat (map k ps) ty i)]
    [(e-pack fs ty i) (e-pack (map (lambda (f) (cons (car f) (k (cdr f)))) fs) ty i)]
    [(e-vlit ps ty i) (e-vlit (map k ps) ty i)]
    [(e-tread n a ty i) (e-tread n (k a) ty i)]
    [(e-call n as ty i) (e-call n (map k as) ty i)]
    [(e-let n ex b ty i) (e-let n (k ex) (k b) ty i)]
    [(e-sget op a ty i) (e-sget op (k a) ty i)]
    [(e-match s cs d ty i)
     (e-match (k s)
              (map (lambda (c) (cons (car c) (k (cdr c)))) cs)
              (and d (k d))
              ty i)]
    [_ e]))

(define (expr-each proc e)
  (proc e)
  (match e
    [(e-binop _ a b _ _) (expr-each proc a) (expr-each proc b)]
    [(e-unop _ a _ _) (expr-each proc a)]
    [(e-mux c t f _ _) (expr-each proc c) (expr-each proc t) (expr-each proc f)]
    [(e-field b _ _ _) (expr-each proc b)]
    [(e-idx b i _ _) (expr-each proc b) (expr-each proc i)]
    [(e-cast _ a _ _) (expr-each proc a)]
    [(e-slice a _ _ _ _) (expr-each proc a)]
    [(e-cat ps _ _) (for-each (lambda (p) (expr-each proc p)) ps)]
    [(e-pack fs _ _) (for-each (lambda (f) (expr-each proc (cdr f))) fs)]
    [(e-vlit ps _ _) (for-each (lambda (p) (expr-each proc p)) ps)]
    [(e-tread _ a _ _) (expr-each proc a)]
    [(e-call _ as _ _) (for-each (lambda (a) (expr-each proc a)) as)]
    [(e-let _ ex b _ _) (expr-each proc ex) (expr-each proc b)]
    [(e-sget _ a _ _) (expr-each proc a)]
    [(e-match s cs d _ _)
     (expr-each proc s)
     (for-each (lambda (c) (expr-each proc (cdr c))) cs)
     (when d (expr-each proc d))]
    [_ (void)]))

(define (expr-equal? a b)
  (equal? (strip a) (strip b)))

(define (strip e)
  (match e
    [(e-ref n t _) (list 'ref n (ty->string t))]
    [(e-child i p t _) (list 'child i p (ty->string t))]
    [(e-lit v t _) (list 'lit v (ty->string t))]
    [(e-binop op a b t _) (list op (strip a) (strip b) (ty->string t))]
    [(e-unop op a t _) (list op (strip a) (ty->string t))]
    [(e-mux c t f ty _) (list 'mux (strip c) (strip t) (strip f) (ty->string ty))]
    [(e-field b f ty _) (list 'field (strip b) f (ty->string ty))]
    [(e-idx b i ty _) (list 'idx (strip b) (strip i) (ty->string ty))]
    [(e-cast k a ty _) (list k (strip a) (ty->string ty))]
    [(e-slice a hi lo ty _) (list 'slice (strip a) hi lo (ty->string ty))]
    [(e-cat ps ty _) (list 'cat (map strip ps) (ty->string ty))]
    [(e-pack fs ty _) (list 'pack (map (lambda (f) (list (car f) (strip (cdr f)))) fs))]
    [(e-vlit ps ty _) (list 'vlit (map strip ps))]
    [(e-tread n a ty _) (list 'tread n (strip a))]
    [(e-rdata n ty _) (list 'rdata n)]
    [(e-call n as ty _) (list 'call n (map strip as))]
    [(e-let n ex b ty _) (list 'let n (strip ex) (strip b))]
    [(e-sget op a ty _) (list op (strip a))]
    [(e-match s cs d ty _)
     (list 'match (strip s) (map (lambda (c) (list (car c) (strip (cdr c)))) cs)
           (and d (strip d)))]
    [(e-bad _ _) '(bad)]
    [_ (list 'other e)]))

(define (stmt-exprs-map proc st)
  (match st
    [(st-set r e i) (st-set r (proc e) i)]
    [(st-twrite t a d i) (st-twrite t (proc a) (proc d) i)]
    [(st-tread t a i) (st-tread t (proc a) i)]
    [(st-drive in p e i) (st-drive in p (proc e) i)]
    [(st-log lv parts i)
     (st-log lv (map (lambda (p)
                       (if (eq? (car p) 'val) (list 'val (proc (cadr p))) p))
                     parts) i)]
    [(st-check e m i) (st-check (proc e) m i)]
    [(st-finish i) st]
    [(st-let bs body i)
     (st-let (map (lambda (b) (list (car b) (proc (cadr b)))) bs)
             (map (lambda (s) (stmt-exprs-map proc s)) body)
             i)]))

(define (lit0 info)
  (e-lit 0 (ty-uint 1) info))

(define (lit-n v ty info)
  (e-lit v ty info))

(define (e-or as info)
  (match as
    ['() (e-lit 0 (ty-uint 1) info)]
    [(list a) a]
    [(cons a r) (e-binop 'or a (e-or r info) (ty-uint 1) info)]))

(define (e-mux* c t f info)
  (e-mux c t f (expr-ty t) info))
