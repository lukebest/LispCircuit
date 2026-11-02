#lang racket
;; Compile-time arithmetic and the restricted namespace macros evaluate in.

(require "diag.rkt")
(provide meta-namespace
         symcat-parts
         log2-int
         clog2-int
         meta-error)

(define (meta-error . args)
  (fail! (diag "ERR_MACRO" "defmacro" "Fix the macro body"
               #f #f (apply format args) #f #f #f #f)))

(define (symcat-parts . parts)
  (string->symbol
   (apply string-append
          (for/list ([p parts])
            (cond
              [(symbol? p) (symbol->string p)]
              [(exact-integer? p) (number->string p)]
              [(string? p) p]
              [else (meta-error "symcat cannot stringify ~a" p)])))))

(define (log2-int n)
  (unless (and (exact-integer? n) (>= n 1) (= (bitwise-and n (sub1 n)) 0))
    (meta-error "log2 expects a positive power of two, got ~a" n))
  (sub1 (integer-length n)))

(define (clog2-int n)
  (unless (and (exact-integer? n) (>= n 1))
    (meta-error "clog2 expects a positive integer, got ~a" n))
  (if (<= n 1) 0 (integer-length (sub1 n))))

(define (gen-for-fn lo hi proc)
  (unless (and (exact-integer? lo) (exact-integer? hi))
    (meta-error "gen-for bounds must be integers"))
  (for/list ([i (in-range lo hi)]) (proc i)))

(define (cat-for-fn lo hi proc)
  (cons 'cat (gen-for-fn lo hi proc)))

(define (reduce-tree-fn op lo hi proc)
  (define es (gen-for-fn lo hi proc))
  (when (null? es) (meta-error "reduce-tree over an empty range"))
  (let bal ([es es])
    (match es
      [(list e) e]
      [else
       (define mid (quotient (length es) 2))
       (list op (bal (take es mid)) (bal (drop es mid)))])))

(define meta-namespace
  (let ([ns (make-base-namespace)])
    (parameterize ([current-namespace ns])
      (namespace-require 'racket/base)
      (namespace-require 'racket/list))
    (for ([b (list (cons 't #t)
                   (cons 'nil #f)
                   (cons 'symcat symcat-parts)
                   (cons 'log2 log2-int)
                   (cons 'clog2 clog2-int)
                   (cons 'gen-for gen-for-fn)
                   (cons 'cat-for cat-for-fn)
                   (cons 'reduce-tree reduce-tree-fn))])
      (namespace-set-variable-value! (car b) (cdr b) #t ns))
    ns))
