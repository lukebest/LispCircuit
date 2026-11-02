#lang racket
;; Cycle-accurate ESL interpreter.
;; One logged cycle is: Eval outputs, Work, Check, Xfer.
;; A silent reset cycle runs first so synchronous resets match the SV backend.

(require json
         "diag.rkt" "ast.rkt" "types.rkt" "bits.rkt" "flatten.rkt" "comb-loop.rkt" "vcd.rkt" "nhir.rkt")
(provide simulate sim-result sim-result-logs sim-result-cycles)

(struct sim-result (logs cycles) #:transparent)

(define (zero-state flat)
  (for/fold ([st (hash)]) ([t (flatnet-tables flat)])
    (define mem (build-vector (ftable-depth t)
                              (lambda (_) (zero-value (ftable-elem-ty t)))))
    (define st1 (hash-set st (ftable-name t) mem))
    (if (ftable-rdata t)
        (hash-set st1 (ftable-rdata t) (zero-value (ftable-elem-ty t)))
        st1)))

(define (init-state flat)
  (for/fold ([st (zero-state flat)]) ([r (flatnet-regs flat)])
    (hash-set st (freg-name r) (freg-init r))))

(define (mems-of st flat)
  (for/hash ([t (flatnet-tables flat)])
    (values (ftable-name t) (hash-ref st (ftable-name t)))))

(define (eval-env st flat order)
  (define mems (mems-of st flat))
  (for/fold ([env st]) ([w order])
    (hash-set env (fwire-name w) (eval-expr (fwire-expr w) env mems))))

(define (ev e env mems)
  (eval-expr e env mems))

(define (fires? g env mems)
  (not (zero? (ev g env mems))))

(define (snapshot st flat)
  (for/hash ([r (flatnet-regs flat)])
    (values (freg-name r)
            (fmt-val (hash-ref st (freg-name r)) (freg-ty r)))))

(define (fail-check info cyc msg st flat)
  (define snap (snapshot st flat))
  (fail! (diag-at "ERR_CHECK" info
                  #:message (format "cycle ~a: ~a" cyc msg)
                  #:suggestion (jsexpr->string snap))))

(define (log-line cyc level kvs)
  (format "[cyc ~a] ~a~a"
          cyc level
          (apply string-append
                 (for/list ([kv kvs])
                   (format " ~a=~a" (car kv) (cdr kv))))))

(define (side-logs sides env mems)
  (for/fold ([lines '()] [finish? #f]) ([s sides])
    (cond
      [(not (fires? (hside-guard s) env mems)) (values lines finish?)]
      [(eq? (hside-kind s) 'log)
       (match-define (list level parts) (hside-data s))
       (define kvs
         (let loop ([ps parts] [key #f])
           (cond
             [(null? ps) '()]
             [(eq? (car (car ps)) 'key) (loop (cdr ps) (cadr (car ps)))]
             [else (cons (cons key (fmt-val (ev (cadr (car ps)) env mems) (expr-ty (cadr (car ps)))))
                         (loop (cdr ps) #f))])))
       (values (append lines (list (log-line 0 level kvs))) finish?)]
      [(eq? (hside-kind s) 'finish) (values lines #t)]
      [else (values lines finish?)])))

;; log-line cycle is filled by the caller; side-logs uses 0 as a placeholder.
(define (renumber lines cyc)
  (map (lambda (ln) (regexp-replace #rx"^\\[cyc 0\\]" ln (format "[cyc ~a]" cyc))) lines))

(define (check-sides! sides env mems st flat cyc)
  (for ([s sides] #:when (eq? (hside-kind s) 'check))
    (when (fires? (hside-guard s) env mems)
      (match-define (list expr msg) (hside-data s))
      (when (zero? (ev expr env mems))
        (fail-check (hside-info s) cyc msg st flat)))))

(define (check-exclusive! flat env mems st cyc)
  (for ([r (flatnet-regs flat)] #:when (memq (freg-mode r) '(exclusive cf)))
    (define n (count (lambda (g) (fires? g env mems)) (freg-guards r)))
    (when (> n 1)
      (fail-check (freg-info r) cyc
                  (format "conflicting rules both fired for ~a (~a)" (freg-name r) (freg-mode r))
                  st flat))))

(define (xfer st flat env mems #:reset? reset?)
  (define new
    (for/fold ([st st]) ([r (flatnet-regs flat)])
      (define hold (hash-ref st (freg-name r)))
      (define val
        (cond
          [(and reset? (not (freg-reset-less? r))) (freg-init r)]
          [(fires? (freg-we r) env mems) (ev (freg-next r) env mems)]
          [else hold]))
      (hash-set st (freg-name r) val)))
  (for/fold ([st new]) ([t (flatnet-tables flat)])
    (define old (hash-ref st (ftable-name t)))
    (define mem (vector-copy old))
    (define st1
      (if (and (ftable-rdata t) (= (ftable-latency t) 1))
          (hash-set st (ftable-rdata t)
                    (if reset?
                        (zero-value (ftable-elem-ty t))
                        (if (fires? (ftable-ren t) env mems)
                            (let ([a (ev (ftable-raddr t) env mems)])
                              (vector-ref old a))
                            (hash-ref st (ftable-rdata t)))))
          st))
    (when (fires? (ftable-wen t) env mems)
      (define a (ev (ftable-waddr t) env mems))
      (define d (ev (ftable-wdata t) env mems))
      (vector-set! mem a d))
    (hash-set st1 (ftable-name t) mem)))

(define (port-env st flat)
  ;; Port wires are not in the register state. Eval needs them, and VCD
  ;; reads them from the env after Eval. Keep the last env for dumping.
  st)

(define (simulate flat
                  #:cycles cycles
                  #:top-name [top-name "top"]
                  #:vcd [vcd #f]
                  #:emit [emit void])
  (define order (topo-order flat))
  (define st0 (init-state flat))
  ;; Silent reset cycle: synchronous resets fire, reset-less regs update.
  (define env0 (eval-env st0 flat order))
  (define st (xfer st0 flat env0 (mems-of st0 flat) #:reset? #t))
  (define dump (and vcd (open-vcd vcd flat (eval-env st flat order) top-name)))
  (define logs '())
  (define ran
    (let loop ([cyc 0] [st st])
      (cond
        [(>= cyc cycles) cyc]
        [else
         (define env (eval-env st flat order))
         (define mems (mems-of st flat))
         (check-sides! (flatnet-sides flat) env mems st flat cyc)
         (check-exclusive! flat env mems st cyc)
         (define-values (lines finish?) (side-logs (flatnet-sides flat) env mems))
         (define new-lines (renumber lines cyc))
         (for-each emit new-lines)
         (set! logs (append logs new-lines))
         (define st2 (xfer st flat env mems #:reset? #f))
         (when dump (vcd-change dump (* (add1 cyc) 10) flat (eval-env st2 flat order)))
         (if finish? (add1 cyc) (loop (add1 cyc) st2))])))
  (when dump (vcd-close dump))
  (sim-result logs ran))
