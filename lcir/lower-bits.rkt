#lang racket
;; Lower a flattened netlist to packed bit-vector operations.
;;
;; Every value becomes a raw bit pattern of a known width: bundles and
;; vectors are packed (first field / element 0 in the high bits, as in
;; bits.rkt `value->raw`), `let` is substituted, sint is two's complement.
;; The C++ and SMT backends both print this IR, so they share one lowering
;; whose reference semantics are ESL's `eval-expr`.
;;
;; IR node: (bv op w args), w = result width. Ops:
;;   const (v)            var (name)          tread (table addr)
;;   add sub mul and or xor (a b)             not (a)
;;   zext sext (a)  -- to width w             extract (a lo)  -- w bits from lo
;;   concat (a ...)  -- first arg high        ite (c t f)
;;   shl lshr ashr (a b)  -- amount b, result 0 / sign fill when b >= w
;;   eq ult ule slt sle (a b)  -- w = 1

(require "ast.rkt" "types.rkt" "bits.rkt" "diag.rkt" "flatten.rkt" "nhir.rkt" "comb-loop.rkt")
(provide (struct-out bv)
         (struct-out lnet)
         (struct-out lreg)
         (struct-out lwire)
         (struct-out ltable)
         (struct-out llog)
         (struct-out lcheck)
         lower-net
         raw-of)

(struct bv (op w args) #:transparent)

(struct lnet (regs wires tables logs checks finishes excl) #:transparent)
(struct lreg (name ty init reset-less? we next) #:transparent)       ; init: raw integer
(struct lwire (name ty expr) #:transparent)                          ; topological order
(struct ltable (name depth ty latency rdata wen waddr wdata ren raddr) #:transparent)
(struct llog (guard level parts) #:transparent)    ; parts: (list (cons key (cons ty bv)) ...)
(struct lcheck (guard expr msg) #:transparent)
;; excl: (list (list reg-name mode (list guard ...))) for every register with
;; two or more writer rules; mode is prio, exclusive or cf.

(define (raw-of v t) (value->raw v t))

(define (K w v) (bv 'const w (list (bitwise-and v (sub1 (arithmetic-shift 1 w))))))

(define (resize a w signed?)
  (define aw (bv-w a))
  (cond
    [(= aw w) a]
    [(< w aw) (bv 'extract w (list a 0))]
    [signed? (bv 'sext w (list a))]
    [else (bv 'zext w (list a))]))

(define (bad e what)
  (fail! (diag-at "ERR_BACKEND" (expr-info e)
                  #:message (format "cannot lower ~a to bit vectors" what))))

;; env: symbol -> bv for let-bound names.
(define (lower e [env (hash)])
  (define (L x) (lower x env))
  (define t (expr-ty e))
  (match e
    [(e-lit v ty _) (K (ty-width ty) (raw-of v ty))]
    [(e-ref n ty _) (hash-ref env n (lambda () (bv 'var (ty-width ty) (list n))))]
    [(e-let n ex body _ _) (lower body (hash-set env n (L ex)))]
    [(e-unop op a ty _)
     (define w (ty-width ty))
     (case op
       [(not) (bv 'eq 1 (list (L a) (K (bv-w (L a)) 0)))]
       [(~) (bv 'not w (list (resize (L a) w #f)))]
       [(-) (bv 'sub w (list (K w 0) (resize (L a) w (ty-sint? (expr-ty a)))))]
       [else (bad e op)])]
    [(e-binop op a b ty _)
     (define w (ty-width ty))
     (define at (expr-ty a))
     (define sa? (ty-sint? at))
     (define la (L a))
     (define lb (L b))
     (case op
       [(+ - * & \| ^ +w -w *w)
        (define bop (case op [(+ +w) 'add] [(- -w) 'sub] [(* *w) 'mul] [(&) 'and] [(\|) 'or] [(^) 'xor]))
        (bv bop w (list (resize la w sa?) (resize lb w (ty-sint? (expr-ty b)))))]
       [(and) (bv 'and 1 (list (bv 'not 1 (list (bv 'eq 1 (list la (K (bv-w la) 0)))))
                               (bv 'not 1 (list (bv 'eq 1 (list lb (K (bv-w lb) 0)))))))]
       [(or) (bv 'or 1 (list (bv 'not 1 (list (bv 'eq 1 (list la (K (bv-w la) 0)))))
                              (bv 'not 1 (list (bv 'eq 1 (list lb (K (bv-w lb) 0)))))))]
       [(<<) (bv 'shl w (list (resize la w sa?) lb))]
       [(>>) (bv (if sa? 'ashr 'lshr) w (list (resize la w sa?) lb))]
       [(== != < <= > >=)
        (define s? (or sa? (ty-sint? (expr-ty b))))
        (define cw (max (bv-w la) (bv-w lb)))
        (define xa (resize la cw s?))
        (define xb (resize lb cw s?))
        (define lt (if s? 'slt 'ult))
        (define le (if s? 'sle 'ule))
        (case op
          [(==) (bv 'eq 1 (list xa xb))]
          [(!=) (bv 'not 1 (list (bv 'eq 1 (list xa xb))))]
          [(<) (bv lt 1 (list xa xb))]
          [(<=) (bv le 1 (list xa xb))]
          [(>) (bv lt 1 (list xb xa))]
          [(>=) (bv le 1 (list xb xa))])]
       [else (bad e op)])]
    [(e-mux c th el ty _)
     (define lc (L c))
     (bv 'ite (ty-width ty) (list (if (= (bv-w lc) 1) lc (bv 'not 1 (list (bv 'eq 1 (list lc (K (bv-w lc) 0))))))
                                  (L th) (L el)))]
    [(e-cast kind a ty _)
     (define w (ty-width ty))
     (define la (L a))
     (case kind
       [(zext as-uint as-sint) (resize la w #f)]
       [(sext) (resize la w #t)]
       [(trunc) (resize la w #f)]
       [else (bad e kind)])]
    [(e-slice a hi lo ty _) (bv 'extract (ty-width ty) (list (L a) lo))]
    [(e-cat ps ty _) (bv 'concat (ty-width ty) (map L ps))]
    [(e-pack fs ty _) (bv 'concat (ty-width ty) (map (lambda (f) (L (cdr f))) fs))]
    [(e-vlit ps ty _) (bv 'concat (ty-width ty) (map L ps))]
    [(e-field b fname ty _)
     (match-define (ty-bundle fs) (expr-ty b))
     (define after (cdr (memf (lambda (f) (eq? (car f) fname)) fs)))
     (define lo (apply + (map (lambda (f) (ty-width (cdr f))) after)))
     (bv 'extract (ty-width ty) (list (L b) lo))]
    [(e-idx b i ty _)
     (match-define (ty-vec n et) (expr-ty b))
     (define ew (ty-width et))
     (define lb (L b))
     (define (elem k) (bv 'extract ew (list lb (* (- n 1 k) ew))))
     (match i
       [(e-lit v _ _) (elem v)]
       [_
        (define li (L i))
        (for/fold ([acc (elem (sub1 n))]) ([k (in-range (- n 2) -1 -1)])
          (bv 'ite ew (list (bv 'eq 1 (list li (K (bv-w li) k))) (elem k) acc)))])]
    [(e-tread name addr ty _) (bv 'tread (ty-width ty) (list name (L addr)))]
    [_ (bad e (if (struct? e) (vector-ref (struct->vector e) 0) e))]))

(define (lower-net flat)
  (define order (topo-order flat))
  (define regs
    (for/list ([r (flatnet-regs flat)])
      (lreg (freg-name r) (freg-ty r) (raw-of (freg-init r) (freg-ty r)) (freg-reset-less? r)
            (lower (freg-we r)) (lower (freg-next r)))))
  (define wires
    (for/list ([w order])
      (lwire (fwire-name w) (fwire-ty w) (lower (fwire-expr w)))))
  (define tables
    (for/list ([t (flatnet-tables flat)])
      (ltable (ftable-name t) (ftable-depth t) (ftable-elem-ty t) (ftable-latency t) (ftable-rdata t)
              (lower (ftable-wen t)) (lower (ftable-waddr t)) (lower (ftable-wdata t))
              (lower (ftable-ren t)) (lower (ftable-raddr t)))))
  (define sides (flatnet-sides flat))
  (define logs
    (for/list ([s sides] #:when (eq? (hside-kind s) 'log))
      (match-define (list level parts) (hside-data s))
      (llog (lower (hside-guard s)) level
            (let loop ([ps parts] [key #f])
              (cond
                [(null? ps) '()]
                [(eq? (car (car ps)) 'key) (loop (cdr ps) (cadr (car ps)))]
                [else
                 (define ex (cadr (car ps)))
                 (cons (cons (format "~a" key) (cons (expr-ty ex) (lower ex)))
                       (loop (cdr ps) #f))])))))
  (define checks
    (for/list ([s sides] #:when (eq? (hside-kind s) 'check))
      (match-define (list ex msg) (hside-data s))
      (lcheck (lower (hside-guard s)) (lower ex) msg)))
  (define finishes
    (for/list ([s sides] #:when (eq? (hside-kind s) 'finish))
      (lower (hside-guard s))))
  (define excl
    (for/list ([r (flatnet-regs flat)] #:when (>= (length (freg-guards r)) 2))
      (list (freg-name r) (freg-mode r) (map lower (freg-guards r)))))
  (lnet regs wires tables logs checks finishes excl))
