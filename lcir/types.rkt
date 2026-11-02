#lang racket
(require "diag.rkt")
(provide (struct-out ty-uint)
         (struct-out ty-sint)
         (struct-out ty-enum)
         (struct-out ty-bundle)
         (struct-out ty-vec)
         (struct-out ty-stream)
         (struct-out ty-err)
         (struct-out ty-int)
         ty-width
         ty=?
         ty->string
         ty-scalar?
         ty-signed?
         unsized?
         ty-kind
         fits-lit?
         normalize-lit
         clog2
         enum-width
         zero-value)

(struct ty-uint (w) #:transparent)
(struct ty-sint (w) #:transparent)
(struct ty-enum (name variants) #:transparent)
(struct ty-bundle (fields) #:transparent) ;; (listof (cons symbol type))
(struct ty-vec (n elem) #:transparent)
(struct ty-stream (elem) #:transparent)
(struct ty-err () #:transparent)
(struct ty-int () #:transparent) ;; unsized integer literal

(define (clog2 n)
  (cond
    [(not (and (exact-integer? n) (>= n 1)))
     (error 'clog2 "expected positive integer, got ~a" n)]
    [(<= n 1) 0]
    [else (integer-length (sub1 n))]))

(define (enum-width n)
  (max 1 (clog2 (max 1 n))))

(define (ty-width t)
  (match t
    [(ty-uint w) w]
    [(ty-sint w) w]
    [(ty-enum _ vs) (enum-width (length vs))]
    [(ty-bundle fs) (apply + (map (lambda (f) (ty-width (cdr f))) fs))]
    [(ty-vec n e) (* n (ty-width e))]
    [(ty-stream e) (ty-width e)]
    [(ty-err) 0]
    [(ty-int) (error 'ty-width "unsized")]
    [_ (error 'ty-width "bad type ~a" t)]))

(define (ty=? a b)
  (match* (a b)
    [((ty-uint w1) (ty-uint w2)) (= w1 w2)]
    [((ty-sint w1) (ty-sint w2)) (= w1 w2)]
    [((ty-enum n1 _) (ty-enum n2 _)) (eq? n1 n2)]
    [((ty-bundle f1) (ty-bundle f2))
     (and (= (length f1) (length f2))
          (andmap (lambda (x y)
                    (and (eq? (car x) (car y)) (ty=? (cdr x) (cdr y))))
                  f1 f2))]
    [((ty-vec n1 e1) (ty-vec n2 e2)) (and (= n1 n2) (ty=? e1 e2))]
    [((ty-stream e1) (ty-stream e2)) (ty=? e1 e2)]
    [((ty-err) (ty-err)) #t]
    [((ty-int) (ty-int)) #t]
    [(_ _) #f]))

(define (ty->string t)
  (match t
    [(ty-uint w) (format "(uint ~a)" w)]
    [(ty-sint w) (format "(sint ~a)" w)]
    [(ty-enum n _) (symbol->string n)]
    [(ty-bundle fs)
     (format "(bundle~a)"
             (apply string-append
                    (for/list ([f fs])
                      (format " (~a ~a)" (car f) (ty->string (cdr f))))))]
    [(ty-vec n e) (format "(vec ~a ~a)" n (ty->string e))]
    [(ty-stream e) (format "(stream ~a)" (ty->string e))]
    [(ty-err) "<error>"]
    [(ty-int) "<unsized>"]
    [#f "<none>"]
    [_ (format "~a" t)]))

(define (ty-scalar? t)
  (or (ty-uint? t) (ty-sint? t) (ty-enum? t)))

(define (ty-signed? t)
  (ty-sint? t))

(define (unsized? t)
  (or (eq? t #f) (ty-int? t)))

(define (ty-kind t)
  (cond
    [(ty-uint? t) 'uint]
    [(ty-sint? t) 'sint]
    [(ty-enum? t) 'enum]
    [(ty-bundle? t) 'bundle]
    [(ty-vec? t) 'vec]
    [(ty-stream? t) 'stream]
    [else 'other]))

(define (fits-lit? v t)
  (match t
    [(ty-uint w)
     (and (exact-integer? v) (>= v 0) (< v (expt 2 w)))]
    [(ty-sint w)
     (and (exact-integer? v)
          (>= v (- (expt 2 (sub1 w))))
          (< v (expt 2 (sub1 w))))]
    [(ty-enum _ vs)
     (and (exact-integer? v) (>= v 0) (< v (length vs)))]
    [_ #f]))

(define (normalize-lit v t)
  v)

(define (zero-value t)
  (match t
    [(or (ty-uint _) (ty-sint _) (ty-enum _ _)) 0]
    [(ty-bundle fs)
     (make-immutable-hash
      (for/list ([f fs]) (cons (car f) (zero-value (cdr f)))))]
    [(ty-vec n e)
     (build-vector n (lambda (_) (zero-value e)))]
    [(ty-stream e) (zero-value e)]
    [(ty-err) 0]
    [_ 0]))
