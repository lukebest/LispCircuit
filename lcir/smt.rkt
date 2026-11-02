#lang racket
;; Target 4: SMT-LIB v2 (QF_ABV) for Z3 or any SMT-LIB solver.
;;
;; Query 1, BMC: unroll K cycles from the post-reset state (same semantics as
;; esl.rkt). sat means some `check` fails, or two writers that were declared
;; :conflict-free / judged exclusive fire together, within K cycles.
;; When the top is a module rather than a system, its input ports are
;; unconstrained per cycle, so the result holds for every input sequence.
;;
;; Query 2..n, writer exclusivity: for each register with several writer
;; rules, are two guards satisfiable together over an unconstrained state?
;; unsat proves the rules are combinationally mutually exclusive.

(require "lower-bits.rkt" "types.rkt" "diag.rkt" "flatten.rkt")
(provide emit-smt-text run-z3 smt-report-lines)

(define (bvlit v w) (format "(_ bv~a ~a)" v w))
(define (sym name k) (format "|~a@~a|" name k))
(define (sort w) (format "(_ BitVec ~a)" w))
(define (addr-w depth) (max 1 (clog2 depth)))

(define (resize-term t from to signed?)
  (cond
    [(= from to) t]
    [(< to from) (format "((_ extract ~a 0) ~a)" (sub1 to) t)]
    [else (format "((_ ~a ~a) ~a)" (if signed? "sign_extend" "zero_extend") (- to from) t)]))

;; ref: symbol -> term; mem: table name -> (cons term addr-width)
(define (term e ref mem)
  (define (a i) (term (list-ref (bv-args e) i) ref mem))
  (define (aw i) (bv-w (list-ref (bv-args e) i)))
  (define w (bv-w e))
  (define (bool->bv b) (format "(ite ~a #b1 #b0)" b))
  (match (bv-op e)
    ['const (bvlit (car (bv-args e)) w)]
    ['var (ref (car (bv-args e)))]
    ['tread
     (match-define (cons m aw*) (mem (car (bv-args e))))
     (define ad (cadr (bv-args e)))
     (format "(select ~a ~a)" m (resize-term (term ad ref mem) (bv-w ad) aw* #f))]
    ['add (format "(bvadd ~a ~a)" (a 0) (a 1))]
    ['sub (format "(bvsub ~a ~a)" (a 0) (a 1))]
    ['mul (format "(bvmul ~a ~a)" (a 0) (a 1))]
    ['and (format "(bvand ~a ~a)" (a 0) (a 1))]
    ['or (format "(bvor ~a ~a)" (a 0) (a 1))]
    ['xor (format "(bvxor ~a ~a)" (a 0) (a 1))]
    ['not (format "(bvnot ~a)" (a 0))]
    ['zext (resize-term (a 0) (aw 0) w #f)]
    ['sext (resize-term (a 0) (aw 0) w #t)]
    ['extract
     (define lo (cadr (bv-args e)))
     (format "((_ extract ~a ~a) ~a)" (+ lo w -1) lo (a 0))]
    ['concat
     (define ts (map (lambda (x) (term x ref mem)) (bv-args e)))
     (let loop ([ts ts])
       (if (null? (cdr ts)) (car ts) (format "(concat ~a ~a)" (car ts) (loop (cdr ts)))))]
    ['ite (format "(ite (= ~a #b1) ~a ~a)" (a 0) (a 1) (a 2))]
    [(or 'shl 'lshr 'ashr)
     ;; Shift in a width wide enough for the amount, then keep the low w bits:
     ;; this gives 0 / sign fill when the amount is >= w, like ESL.
     (define m (max w (aw 1)))
     (define x (resize-term (a 0) w m (eq? (bv-op e) 'ashr)))
     (define b (resize-term (a 1) (aw 1) m #f))
     (define op (case (bv-op e) [(shl) "bvshl"] [(lshr) "bvlshr"] [(ashr) "bvashr"]))
     (resize-term (format "(~a ~a ~a)" op x b) m w #f)]
    ['eq (bool->bv (format "(= ~a ~a)" (a 0) (a 1)))]
    ['ult (bool->bv (format "(bvult ~a ~a)" (a 0) (a 1)))]
    ['ule (bool->bv (format "(bvule ~a ~a)" (a 0) (a 1)))]
    ['slt (bool->bv (format "(bvslt ~a ~a)" (a 0) (a 1)))]
    ['sle (bool->bv (format "(bvsle ~a ~a)" (a 0) (a 1)))]))

(define (true? t) (format "(= ~a #b1)" t))
(define (or* ts) (cond [(null? ts) "false"] [(null? (cdr ts)) (car ts)] [else (format "(or ~a)" (string-join ts " "))]))
(define (and* ts) (cond [(null? ts) "true"] [(null? (cdr ts)) (car ts)] [else (format "(and ~a)" (string-join ts " "))]))

;; Emits definitions for one cycle k: wires, and returns (values ref mem).
(define (emit-cycle! p net k free-inputs)
  (define wire-ty (for/hash ([w (lnet-wires net)]) (values (lwire-name w) (ty-width (lwire-ty w)))))
  (define (ref n) (sym n k))
  (define (mem n)
    (define t (findf (lambda (t) (eq? (ltable-name t) n)) (lnet-tables net)))
    (cons (sym n k) (addr-w (ltable-depth t))))
  (for ([w (lnet-wires net)])
    (define nm (lwire-name w))
    (if (memq nm free-inputs)
        (p (format "(declare-const ~a ~a)" (sym nm k) (sort (hash-ref wire-ty nm))))
        (p (format "(define-fun ~a () ~a ~a)" (sym nm k) (sort (hash-ref wire-ty nm))
                   (term (lwire-expr w) ref mem)))))
  (values ref mem))

(define (arr-sort t)
  (format "(Array ~a ~a)" (sort (addr-w (ltable-depth t))) (sort (ty-width (ltable-ty t)))))

;; Defines state `to` from cycle k. reset? selects the silent reset cycle.
(define (emit-next! p net k to ref mem reset?)
  (for ([r (lnet-regs net)])
    (define w (ty-width (lreg-ty r)))
    (define held (sym (lreg-name r) k))
    (define upd (format "(ite ~a ~a ~a)" (true? (term (lreg-we r) ref mem)) (term (lreg-next r) ref mem) held))
    (p (format "(define-fun ~a () ~a ~a)" (sym (lreg-name r) to) (sort w)
               (if (and reset? (not (lreg-reset-less? r))) (bvlit (lreg-init r) w) upd))))
  (for ([t (lnet-tables net)])
    (define aw (addr-w (ltable-depth t)))
    (define ew (ty-width (ltable-ty t)))
    (define m (sym (ltable-name t) k))
    (define (addr e) (resize-term (term e ref mem) (bv-w e) aw #f))
    (when (ltable-rdata t)
      (p (format "(define-fun ~a () ~a ~a)" (sym (ltable-rdata t) to) (sort ew)
                 (if reset?
                     (bvlit 0 ew)
                     (format "(ite ~a (select ~a ~a) ~a)" (true? (term (ltable-ren t) ref mem))
                             m (addr (ltable-raddr t)) (sym (ltable-rdata t) k))))))
    (p (format "(define-fun ~a () ~a (ite ~a (store ~a ~a ~a) ~a))" (sym (ltable-name t) to) (arr-sort t)
               (true? (term (ltable-wen t) ref mem)) m (addr (ltable-waddr t)) (term (ltable-wdata t) ref mem) m))))

(define (two-of ts)
  (or* (for*/list ([i (in-range (length ts))] [j (in-range (add1 i) (length ts))])
         (format "(and ~a ~a)" (list-ref ts i) (list-ref ts j)))))

;; Returns the SMT-LIB text. Each (check-sat) is preceded by (echo "label").
(define (emit-smt-text flat #:depth depth #:top-name top-name #:free-inputs [free-inputs '()])
  (define net (lower-net flat))
  (define o (open-output-string))
  (define (p s) (displayln s o))
  (p (format "; Generated by LispCircuit (Target 4: SMT-LIB v2). top=~a depth=~a" top-name depth))
  (p "(set-logic QF_ABV)")
  ;; ---- BMC
  (p "(push 1)")
  (for ([r (lnet-regs net)])
    (p (format "(define-fun ~a () ~a ~a)" (sym (lreg-name r) "init") (sort (ty-width (lreg-ty r)))
               (bvlit (lreg-init r) (ty-width (lreg-ty r))))))
  (for ([t (lnet-tables net)])
    (p (format "(define-fun ~a () ~a ((as const ~a) ~a))" (sym (ltable-name t) "init") (arr-sort t) (arr-sort t)
               (bvlit 0 (ty-width (ltable-ty t)))))
    (when (ltable-rdata t)
      (p (format "(define-fun ~a () ~a ~a)" (sym (ltable-rdata t) "init") (sort (ty-width (ltable-ty t)))
                 (bvlit 0 (ty-width (ltable-ty t)))))))
  ;; reset cycle "init" -> cycle 0
  (p "; silent reset cycle")
  (let-values ([(ref mem) (emit-cycle! p net "init" free-inputs)])
    (emit-next! p net "init" 0 ref mem #t))
  (define bad '())
  (define stop '())
  (for ([k (in-range depth)])
    (p (format "; cycle ~a" k))
    (define-values (ref mem) (emit-cycle! p net k free-inputs))
    (define fails
      (append
       (for/list ([c (lnet-checks net)])
         (format "(and ~a (not ~a))" (true? (term (lcheck-guard c) ref mem)) (true? (term (lcheck-expr c) ref mem))))
       (for/list ([x (lnet-excl net)] #:when (memq (cadr x) '(exclusive cf)))
         (two-of (map (lambda (g) (true? (term g ref mem))) (caddr x))))))
    (define fin (map (lambda (g) (true? (term g ref mem))) (lnet-finishes net)))
    (p (format "(define-fun |fail@~a| () Bool ~a)" k (or* fails)))
    (p (format "(define-fun |finish@~a| () Bool ~a)" k (or* fin)))
    (set! bad (cons (and* (append (for/list ([j (in-range k)]) (format "(not |fail@~a|) (not |finish@~a|)" j j))
                                  (list (format "|fail@~a|" k))))
                    bad))
    (when (< k (sub1 depth)) (emit-next! p net k (add1 k) ref mem #f)))
  (p (format "(assert ~a)" (or* (reverse bad))))
  (p "(echo \"bmc\")")
  (p "(check-sat)")
  (p "(pop 1)")
  ;; ---- writer exclusivity over unconstrained state
  (for ([g (lnet-excl net)])
    (match-define (list reg-name mode guards) g)
    (p "(push 1)")
    (for ([r (lnet-regs net)])
      (p (format "(declare-const ~a ~a)" (sym (lreg-name r) "free") (sort (ty-width (lreg-ty r))))))
    (for ([t (lnet-tables net)])
      (p (format "(declare-const ~a ~a)" (sym (ltable-name t) "free") (arr-sort t)))
      (when (ltable-rdata t)
        (p (format "(declare-const ~a ~a)" (sym (ltable-rdata t) "free") (sort (ty-width (ltable-ty t)))))))
    (define-values (ref mem) (emit-cycle! p net "free" free-inputs))
    (p (format "(assert ~a)" (two-of (map (lambda (gx) (true? (term gx ref mem))) guards))))
    (p (format "(echo \"excl ~a ~a\")" reg-name mode))
    (p "(check-sat)")
    (p "(pop 1)"))
  (get-output-string o))

;; ---------------------------------------------------------------- z3
(define (run-z3 text)
  (define z3 (find-executable-path "z3"))
  (unless z3
    (fail! (diag-at "ERR_BACKEND" (info "smt" #f #f #f)
                    #:message "z3 is not installed"
                    #:suggestion "Install z3 (e.g. `pacman -S z3`) or run the .smt2 file with another solver")))
  (define-values (sp out in err) (subprocess #f #f #f z3 "-in" "-smt2"))
  (write-string text in)
  (close-output-port in)
  (define lines (string-split (port->string out) "\n"))
  (define err-text (port->string err))
  (subprocess-wait sp)
  (close-input-port out)
  (close-input-port err)
  (define results
    (let loop ([ls lines])
      (cond
        [(or (null? ls) (null? (cdr ls))) '()]
        [(regexp-match? #rx"^\\(error" (car ls))
         (fail! (diag-at "ERR_BACKEND" (info "smt" #f #f #f) #:message (format "solver error: ~a" (car ls))))]
        [else (cons (cons (car ls) (cadr ls)) (loop (cddr ls)))])))
  (define bmc (assoc "bmc" results))
  (hasheq 'status (cond [(not bmc) "unknown"] [(equal? (cdr bmc) "unsat") "pass"] [(equal? (cdr bmc) "sat") "fail"] [else "unknown"])
          'results (for/list ([r results]) (hasheq 'query (car r) 'result (cdr r)))))

(define (smt-report-lines res)
  (cons (format "bmc: ~a" (hash-ref res 'status))
        (for/list ([r (hash-ref res 'results)])
          (define q (hash-ref r 'query))
          (define v (hash-ref r 'result))
          (cond
            [(equal? q "bmc") (format "  ~a: ~a (~a)" q v (if (equal? v "unsat") "no check can fail" "a check can fail"))]
            [else (format "  ~a: ~a (~a)" q v (if (equal? v "unsat") "writers proven mutually exclusive" "writers may fire together"))]))))
