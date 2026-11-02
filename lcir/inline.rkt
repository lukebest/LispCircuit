#lang racket
;; Inline defalgo calls, then lift let bindings to named wires so the
;; scheduler and the backends see a flat expression DAG.

(require "diag.rkt" "ast.rkt" "types.rkt")
(provide inline-module lift-module)

(define (subst e env)
  (match e
    [(e-ref n t i)
     (if (hash-has-key? env n) (hash-ref env n) e)]
    [(e-let n ex body t i)
     (e-let n (subst ex env) (subst body (hash-remove env n)) t i)]
    [else (expr-map-kids (lambda (k) (subst k env)) e)]))

(define (inline-expr e algos stack)
  (match e
    [(e-call name args ty info)
     (when (memq name stack)
       (fail! (diag-at "ERR_PARSE" info
                       #:message (format "recursive defalgo ~a" name)
                       #:suggestion "Hardware algorithms must be acyclic")))
     (define algo (hash-ref algos name #f))
     (unless algo
       (fail! (diag-at "ERR_UNDEFINED" info #:message (format "unknown algo ~a" name))))
     (define args2 (map (lambda (a) (inline-expr a algos stack)) args))
     (define body (inline-expr (aalgo-body algo) algos (cons name stack)))
     (define env
       (for/hash ([p (aalgo-params algo)] [a args2])
         (values (car p) a)))
     (subst body env)]
    [else (expr-map-kids (lambda (k) (inline-expr k algos stack)) e)]))

(define (inline-module m extra-algos)
  (define algos
    (for/fold ([h extra-algos]) ([a (amod-algos m)])
      (hash-set h (aalgo-name a) a)))
  (define (ie e) (inline-expr e algos '()))
  (struct-copy amod m
               [wires (map (lambda (w) (struct-copy awire w [expr (ie (awire-expr w))])) (amod-wires m))]
               [regs (map (lambda (r) (struct-copy areg r [init (ie (areg-init r))])) (amod-regs m))]
               [rules (map (lambda (r)
                             (struct-copy arule r
                                          [guard (ie (arule-guard r))]
                                          [body (map (lambda (s) (stmt-exprs-map ie s)) (arule-body r))]))
                           (amod-rules m))]
               [insts (map (lambda (i)
                             (struct-copy ainst i
                                          [connects (for/hash ([(k v) (in-hash (ainst-connects i))])
                                                     (values k (ie v)))]))
                           (amod-insts m))]))

(define (lift-expr e wires)
  (match e
    [(e-let name ex body ty info)
     (define-values (ex2 w1) (lift-expr ex wires))
     (define-values (body2 w2) (lift-expr body w1))
     (values body2 (append w2 (list (awire name (expr-ty ex2) ex2 info))))]
    [else
     (define acc (box wires))
     (define e2
       (expr-map-kids
        (lambda (k)
          (define-values (k2 w) (lift-expr k (unbox acc)))
          (set-box! acc w)
          k2)
        e))
     (values e2 (unbox acc))]))

(define (lift-stmts stmts wires)
  (for/fold ([out '()] [wires wires]) ([st stmts])
    (define-values (sts w2) (lift-stmt st wires))
    (values (append out sts) w2)))

(define (lift-stmt st wires)
  (match st
    [(st-let bs body info)
     (define w1
       (for/fold ([w wires]) ([b bs])
         (define-values (e2 w2) (lift-expr (cadr b) w))
         (append w2 (list (awire (car b) (expr-ty e2) e2 (expr-info e2))))))
     (lift-stmts body w1)]
    [else
     (define acc (box wires))
     (define st2
       (stmt-exprs-map
        (lambda (e)
          (define-values (e2 w) (lift-expr e (unbox acc)))
          (set-box! acc w)
          e2)
        st))
     (values (list st2) (unbox acc))]))

(define (lift-module m)
  (define wires (amod-wires m))
  (define-values (wires2 regs)
    (for/fold ([w wires] [rs '()]) ([r (amod-regs m)])
      (define-values (e2 w2) (lift-expr (areg-init r) w))
      (values w2 (append rs (list (struct-copy areg r [init e2]))))))
  (define-values (wires3 rules)
    (for/fold ([w wires2] [rs '()]) ([r (amod-rules m)])
      (define-values (g w1) (lift-expr (arule-guard r) w))
      (define-values (body w2) (lift-stmts (arule-body r) w1))
      (values w2 (append rs (list (struct-copy arule r [guard g] [body body]))))))
  (define-values (wires4 insts)
    (for/fold ([w wires3] [is '()]) ([i (amod-insts m)])
      (define-values (cs w2)
        (for/fold ([cs (hash)] [w w]) ([(k v) (in-hash (ainst-connects i))])
          (define-values (v2 w1) (lift-expr v w))
          (values (hash-set cs k v2) w1)))
      (values w2 (append is (list (struct-copy ainst i [connects cs]))))))
  (struct-copy amod m [wires wires4] [regs regs] [rules rules] [insts insts]))
