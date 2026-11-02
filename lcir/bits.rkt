#lang racket
;; Bit-accurate evaluation of typed Core LCIR expressions.
;; Values: exact integers (signed for sint / mathematical for uint),
;; immutable hashes for bundles, vectors for vecs.

(require "ast.rkt" "types.rkt" "diag.rkt")
(provide eval-expr
         eval-const
         fmt-val
         value->raw
         raw->signed
         exn:runtime
         exn:runtime?
         exn:runtime-code
         exn:runtime-text)

(struct exn:runtime exn:fail (code text info) #:transparent)

(define (rt! code text info)
  (raise (exn:runtime text (current-continuation-marks) code text info)))

(define (mask w)
  (sub1 (expt 2 w)))

(define (raw->signed raw w)
  (if (>= raw (expt 2 (sub1 w)))
      (- raw (expt 2 w))
      raw))

(define (value->raw v t)
  (match t
    [(ty-uint _) v]
    [(ty-sint w) (modulo v (expt 2 w))]
    [(ty-enum _ _) v]
    [(ty-bundle fs)
     (for/fold ([acc 0]) ([f fs])
       (define fw (ty-width (cdr f)))
       (+ (* acc (expt 2 fw)) (value->raw (hash-ref v (car f)) (cdr f))))]
    [(ty-vec n e)
     (for/fold ([acc 0]) ([i (in-range n)])
       (+ (* acc (expt 2 (ty-width e))) (value->raw (vector-ref v i) e)))]
    [(ty-err) 0]
    [_ (rt! "ERR_INTERNAL" (format "no bit pattern for ~a" (ty->string t)) #f)]))

(define (as-signed v t)
  (if (ty-sint? t) v (value->raw v t)))

(define (finish-bits raw w signed?)
  (define m (bitwise-and raw (mask w)))
  (if signed? (raw->signed m w) m))

(define (fmt-val v t)
  (match t
    [(ty-enum _ vs)
     (if (and (exact-integer? v) (>= v 0) (< v (length vs)))
         (symbol->string (list-ref vs v))
         (format "~a" v))]
    [(or (ty-uint _) (ty-sint _)) (number->string v)]
    [(ty-bundle fs)
     (format "{~a}"
             (string-join
              (for/list ([f fs])
                (format "~a=~a" (car f) (fmt-val (hash-ref v (car f)) (cdr f))))
              ","))]
    [(ty-vec n e)
     (format "[~a]"
             (string-join
              (for/list ([i (in-range n)]) (fmt-val (vector-ref v i) e))
              ","))]
    [_ (format "~a" v)]))

(define (eval-const e)
  (eval-expr e (hash) (hash)))

(define (eval-expr e env mems)
  (let ev ([e e] [env env])
    (match e
      [(e-lit v _ _) v]
      [(e-ref n _ info)
       (unless (hash-has-key? env n)
         (rt! "ERR_INTERNAL" (format "unbound ~a during eval" n) info))
       (hash-ref env n)]
      [(e-child inst port _ info)
       (define key (string->symbol (format "~a.~a" inst port)))
       (if (hash-has-key? env key)
           (hash-ref env key)
           (rt! "ERR_INTERNAL" (format "unbound ~a.~a during eval" inst port) info))]
      [(e-rdata n _ info)
       (define key (string->symbol (format "~a__rdata" n)))
       (hash-ref env key (lambda () (rt! "ERR_INTERNAL" "missing rdata" info)))]
      [(e-unop op a t info)
       (define av (ev a env))
       (define at (expr-ty a))
       (case op
         [(not) (if (zero? av) 1 0)]
         [(~)
          (define w (ty-width at))
          (finish-bits (bitwise-xor (value->raw av at) (mask w)) w (ty-sint? t))]
         [(-)
          (define w (ty-width t))
          (if (ty-sint? t)
              (finish-bits (value->raw (- av) (ty-sint w)) w #t)
              (modulo (- av) (expt 2 w)))]
         [else (rt! "ERR_INTERNAL" (format "bad unop ~a" op) info)])]
      [(e-binop op a b t info)
       (define av (ev a env))
       (define bv (ev b env))
       (define at (expr-ty a))
       (define bt (expr-ty b))
       (define w (ty-width t))
       (define signed? (ty-sint? t))
       (define (logical f)
         (if (f (not (zero? av)) (not (zero? bv))) 1 0))
       (case op
         [(+) (finish-bits (+ (value->raw av at) (value->raw bv bt)) w signed?)]
         [(-) (finish-bits (- (value->raw av at) (value->raw bv bt)) w signed?)]
         [(*) (finish-bits (* (as-signed av at) (as-signed bv bt)) w signed?)]
         [(+w) (if (ty-sint? at) (+ av bv) (+ av bv))]
         [(-w)
          (if (ty-sint? at)
              (- av bv)
              (modulo (- av bv) (expt 2 w)))]
         [(*w) (* (as-signed av at) (as-signed bv bt))]
         [(&) (finish-bits (bitwise-and (value->raw av at) (value->raw bv bt)) w signed?)]
         [(\|) (finish-bits (bitwise-ior (value->raw av at) (value->raw bv bt)) w signed?)]
         [(^) (finish-bits (bitwise-xor (value->raw av at) (value->raw bv bt)) w signed?)]
         [(and) (logical (lambda (x y) (and x y)))]
         [(or) (logical (lambda (x y) (or x y)))]
         [(<< >>)
          (define sh bv)
          (define raw (value->raw av at))
          (define sw (ty-width at))
          (define ss? (ty-sint? at))
          (cond
            [(negative? sh) (rt! "ERR_CHECK" "negative shift" info)]
            [(eq? op '<<)
             (finish-bits (if (>= sh sw) 0 (arithmetic-shift raw sh)) w signed?)]
            [(ty-sint? at)
             (if (>= sh sw)
                 (if (negative? av) -1 0)
                 (arithmetic-shift av (- sh)))]
            [else
             (if (>= sh sw) 0 (arithmetic-shift raw (- sh)))])]
         [(== != < <= > >=)
          (define sa (as-signed av at))
          (define sb (as-signed bv bt))
          ;; Enums and uints compare as unsigned magnitudes; sint as signed.
          (define xa (if (ty-sint? at) sa (value->raw av at)))
          (define xb (if (ty-sint? bt) sb (value->raw bv bt)))
          (define r
            (case op
              [(==) (= xa xb)]
              [(!=) (not (= xa xb))]
              [(<) (< xa xb)]
              [(<=) (<= xa xb)]
              [(>) (> xa xb)]
              [(>=) (>= xa xb)]))
          (if r 1 0)]
         [else (rt! "ERR_INTERNAL" (format "bad binop ~a" op) info)])]
      [(e-mux c t f _ _)
       (if (zero? (ev c env)) (ev f env) (ev t env))]
      [(e-cast kind a t info)
       (define av (ev a env))
       (define at (expr-ty a))
       (define raw (value->raw av at))
       (case kind
         [(zext) raw]
         [(sext) (raw->signed raw (ty-width at))]
         [(trunc) (finish-bits raw (ty-width t) (ty-sint? t))]
         [(as-uint) raw]
         [(as-sint) (raw->signed raw (ty-width t))]
         [else (rt! "ERR_INTERNAL" "bad cast" info)])]
      [(e-slice a hi lo t info)
       (define raw (value->raw (ev a env) (expr-ty a)))
       (bitwise-and (arithmetic-shift raw (- lo)) (mask (ty-width t)))]
      [(e-cat ps t _)
       (for/fold ([acc 0]) ([p ps])
         (define pt (expr-ty p))
         (+ (* acc (expt 2 (ty-width pt))) (value->raw (ev p env) pt)))]
      [(e-field b fname _ info)
       (define h (ev b env))
       (unless (hash? h) (rt! "ERR_INTERNAL" "field of non-bundle" info))
       (hash-ref h fname)]
      [(e-idx b i t info)
       (define vec (ev b env))
       (define iv (ev i env))
       (define n (vector-length vec))
       (unless (and (exact-integer? iv) (>= iv 0) (< iv n))
         (rt! "ERR_CHECK" (format "index ~a outside [0, ~a)" iv n) info))
       (vector-ref vec iv)]
      [(e-pack fs _ _)
       (make-immutable-hash
        (for/list ([f fs]) (cons (car f) (ev (cdr f) env))))]
      [(e-vlit ps _ _)
       (apply vector-immutable (map (lambda (p) (ev p env)) ps))]
      [(e-tread name addr _ info)
       (define mem (hash-ref mems name #f))
       (unless mem (rt! "ERR_INTERNAL" (format "no memory ~a" name) info))
       (define a (ev addr env))
       (unless (and (exact-integer? a) (>= a 0) (< a (vector-length mem)))
         (rt! "ERR_CHECK" (format "table ~a address ~a out of range" name a) info))
       (vector-ref mem a)]
      [(e-let name ex body _ _)
       (ev body (hash-set env name (ev ex env)))]
      [(e-bad _ info) (rt! "ERR_INTERNAL" "evaluated an error expression" info)]
      [(e-call name _ _ info)
       (rt! "ERR_INTERNAL" (format "uninlined call ~a" name) info)]
      [(e-sget op _ _ info)
       (rt! "ERR_INTERNAL" (format "unresolved stream access ~a" op) info)]
      [_ (rt! "ERR_INTERNAL" (format "cannot eval ~a" e) (expr-info e))])))
