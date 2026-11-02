#lang racket
;; SMT backend checks that do not need a solver.
;;
;; For a defsystem top every BMC term is concrete, so a small evaluator for
;; the SMT-LIB subset we emit can decide the query. Its answer must agree
;; with ESL, and the per-cycle wire values must agree with ESL logs. If z3
;; is installed, the same queries are also run through it.

(require racket/runtime-path rackunit
         "../lcir/compile.rkt" "../lcir/flatten.rkt" "../lcir/esl.rkt" "../lcir/nhir.rkt"
         "../lcir/smt.rkt" "../lcir/diag.rkt")

(define-runtime-path examples-dir "../examples")

(define (read-all text)
  (with-input-from-string text
    (lambda () (let loop () (define x (read)) (if (eof-object? x) '() (cons x (loop)))))))

;; Values: (cons n w) for bit vectors, booleans, (cons 'arr hash default) for arrays.
(define (mask n w) (bitwise-and n (sub1 (arithmetic-shift 1 w))))
(define (signed v) (define n (car v)) (define w (cdr v))
  (if (>= n (arithmetic-shift 1 (sub1 w))) (- n (arithmetic-shift 1 w)) n))

(define (ev t env)
  (define (E x) (ev x env))
  (define (bvop f a b) (define x (E a)) (define y (E b)) (cons (mask (f (car x) (car y)) (cdr x)) (cdr x)))
  (match t
    ['true #t]
    ['false #f]
    [(? symbol?) (hash-ref env t (lambda () (error 'smt-eval "unbound ~a" t)))]
    [(? exact-integer?) (cons t 1)] ; #b0 / #b1
    [`(_ ,bv ,w) (cons (string->number (substring (symbol->string bv) 2)) w)]
    [`(ite ,c ,a ,b) (if (E c) (E a) (E b))]
    [`(= ,a ,b) (equal? (E a) (E b))]
    [`(and . ,xs) (andmap E xs)]
    [`(or . ,xs) (ormap E xs)]
    [`(not ,a) (not (E a))]
    [`(bvadd ,a ,b) (bvop + a b)]
    [`(bvsub ,a ,b) (bvop - a b)]
    [`(bvmul ,a ,b) (bvop * a b)]
    [`(bvand ,a ,b) (bvop bitwise-and a b)]
    [`(bvor ,a ,b) (bvop bitwise-ior a b)]
    [`(bvxor ,a ,b) (bvop bitwise-xor a b)]
    [`(bvnot ,a) (define x (E a)) (cons (mask (bitwise-not (car x)) (cdr x)) (cdr x))]
    [`(bvshl ,a ,b) (define x (E a)) (define y (E b))
                    (cons (if (>= (car y) (cdr x)) 0 (mask (arithmetic-shift (car x) (car y)) (cdr x))) (cdr x))]
    [`(bvlshr ,a ,b) (define x (E a)) (define y (E b))
                     (cons (if (>= (car y) (cdr x)) 0 (arithmetic-shift (car x) (- (car y)))) (cdr x))]
    [`(bvashr ,a ,b) (define x (E a)) (define y (E b))
                     (cons (mask (arithmetic-shift (signed x) (- (min (car y) (cdr x)))) (cdr x)) (cdr x))]
    [`(bvult ,a ,b) (< (car (E a)) (car (E b)))]
    [`(bvule ,a ,b) (<= (car (E a)) (car (E b)))]
    [`(bvslt ,a ,b) (< (signed (E a)) (signed (E b)))]
    [`(bvsle ,a ,b) (<= (signed (E a)) (signed (E b)))]
    [`(concat ,a ,b) (define x (E a)) (define y (E b))
                     (cons (+ (arithmetic-shift (car x) (cdr y)) (car y)) (+ (cdr x) (cdr y)))]
    [`((_ extract ,h ,l) ,a) (cons (mask (arithmetic-shift (car (E a)) (- l)) (+ 1 (- h l))) (+ 1 (- h l)))]
    [`((_ zero_extend ,k) ,a) (define x (E a)) (cons (car x) (+ k (cdr x)))]
    [`((_ sign_extend ,k) ,a) (define x (E a)) (cons (mask (signed x) (+ k (cdr x))) (+ k (cdr x)))]
    [`((as const ,_) ,v) (list 'arr (hash) (E v))]
    [`(select ,m ,a) (match (E m) [(list 'arr h d) (hash-ref h (car (E a)) d)])]
    [`(store ,m ,a ,v) (match (E m) [(list 'arr h d) (list 'arr (hash-set h (car (E a)) (E v)) d)])]
    [_ (error 'smt-eval "unsupported term ~s" t)]))

;; Evaluate up to the first check-sat. Returns (values sat? env).
(define (eval-bmc cmds)
  (let loop ([cs cmds] [env (hash)] [asserts '()])
    (match (car cs)
      [`(define-fun ,n () ,_ ,body) (loop (cdr cs) (hash-set env n (ev body env)) asserts)]
      [`(declare-const ,n ,_) (error 'smt-eval "free variable ~a in a system BMC" n)]
      [`(assert ,f) (loop (cdr cs) env (cons (ev f env) asserts))]
      ['(check-sat) (values (andmap values asserts) env)]
      [_ (loop (cdr cs) env asserts)])))

(define (esl-of d cycles)
  (define sys (car (design-systems d)))
  (with-handlers ([exn:lcir? (lambda (e) 'check-failed)])
    (sim-result-logs (simulate (flatten-design sys) #:cycles cycles))))

(define (smt-of d depth)
  (define sys (car (design-systems d)))
  (emit-smt-text (flatten-design sys) #:depth depth #:top-name (symbol->string (hmod-name sys))))

(define z3 (find-executable-path "z3"))

(define (agree! label d depth)
  (define text (smt-of d depth))
  (define-values (sat? env) (eval-bmc (read-all text)))
  (define esl (esl-of d depth))
  (check-equal? sat? (eq? esl 'check-failed) (format "~a depth ~a" label depth))
  (when z3
    (check-equal? (hash-ref (run-z3 text) 'status) (if sat? "fail" "pass") label))
  env)

;; Shipped examples: no check fails; SMT must say unsat.
(for ([n '("counter" "streaming_mac" "fifo_counter" "fsm_enum" "sram_lat1" "stream_pipeline" "datapath_mix" "afifo")])
  (void (agree! n (compile-file (build-path examples-dir (format "~a.lcir" n))) 20)))

;; Wire values per cycle equal ESL log values (datapath coverage).
(let* ([d (compile-file (build-path examples-dir "datapath_mix.lcir"))]
       [env (agree! "datapath_mix" d 12)]
       [ops '(ADD SUB SHL ASR)])
  (for ([ln (esl-of d 12)])
    (match-define (list _ cyc) (regexp-match #rx"^\\[cyc ([0-9]+)\\]" ln))
    (for ([kv (regexp-match* #rx"([a-z]+)=(-?[0-9A-Z]+)" ln #:match-select cdr)])
      (match-define (list k v) kv)
      (define sym (string->symbol (format "~a@~a" (if (equal? k "t") "t" (format "dut__~a" k)) cyc)))
      (define got (hash-ref env sym #f))
      (when got
        (define want (or (index-of ops (string->symbol v)) (string->number v)))
        (check-equal? (car got) (mask want (cdr got)) (format "~a at cycle ~a" k cyc))))))

;; A check that fails at cycle 3, found at depth 4 but not depth 3; a
;; finish before it hides the failure.
(define failing #<<SRC
(defmodule C
  :ports ((out y (uint 4)))
  :state ((c :type (uint 4) :init 0))
  :comb ((assign y c))
  (defrule inc :guard 1 :body ((set! c (+ c 1)))))
(defsystem T
  :instances ((dut C))
  (defrule watch :guard 1 :body ((check (!= dut.y 3) "y reached 3")))
  (defrule stop :guard (== dut.y STOP) :priority 0 :body ((finish))))
SRC
  )
(define (failing-design stop) (compile-source (string-replace failing "STOP" (number->string stop)) #:prims? #f))
(void (agree! "fails@3 depth 4" (failing-design 9) 4))
(void (agree! "fails@3 depth 3" (failing-design 9) 3))
(void (agree! "finish@2 hides fail@3" (failing-design 2) 8))

;; Module top: inputs are free, so the BMC contains declare-const and the
;; writer-exclusivity queries are present.
(let* ([d (compile-file (build-path examples-dir "fifo_counter.lcir"))]
       [m (findf (lambda (h) (eq? (hmod-name h) 'FifoCnt)) (design-modules d))]
       [text (emit-smt-text (flatten-design m) #:depth 3 #:top-name "FifoCnt"
                            #:free-inputs (hmod-input-names m))]
       [cmds (read-all text)])
  (check-true (and (member '(declare-const push@0 (_ BitVec 1)) cmds) #t))
  (check-equal? (count (lambda (c) (equal? c '(check-sat))) cmds) 2)
  (when z3
    (define res (run-z3 text))
    (check-equal? (hash-ref res 'status) "pass")))

(printf "smt smoke ok~a\n" (if z3 " (z3)" " (no z3: solver runs skipped)"))

;; AFIFO formal harness (z3 only): the real property holds for 8 cycles of
;; arbitrary push/pop; a deliberately wrong bound yields a counterexample
;; trace whose last cycle is the failing one.
(when z3
  (define src (file->string (build-path examples-dir "afifo.lcir")))
  (define (prop-result text depth)
    (define d (compile-source text #:file (path->string (build-path examples-dir "afifo.lcir"))))
    (define m (findf (lambda (h) (eq? (hmod-name h) 'AfifoProp)) (design-modules d)))
    (run-z3 (emit-smt-text (flatten-design m) #:depth depth #:top-name "AfifoProp"
                           #:free-inputs (hmod-input-names m))))
  (check-equal? (hash-ref (prop-result src 8) 'status) "pass")
  (define bad (prop-result (string-replace src "(<= (- wcnt rcnt) 4)" "(<= (- wcnt rcnt) 3)") 12))
  (check-equal? (hash-ref bad 'status) "fail")
  (check-true (hash-ref (last (hash-ref bad 'trace)) 'fail))
  (displayln "afifo formal ok"))
