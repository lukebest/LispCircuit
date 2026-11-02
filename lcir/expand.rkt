#lang racket
;; Phase-1 expansion: defmacro (restricted eval), gen-for / cat-for /
;; reduce-tree / symcat / log2 / clog2, and constant folding.

(require "diag.rkt" "reader.rkt" "meta-ns.rkt")
(provide expand-file-forms
         expand-body
         expand-one
         register-macros!
         current-macros
         subst-params
         template-sexps)

(define current-macros (make-parameter (hash)))

(define macro-depth (make-parameter 0))

(define (register-macros! forms)
  (define macs (current-macros))
  (for ([f forms])
    (when (eq? (form-head f) 'defmacro)
      (define d (unL f))
      (match d
        [(list _ name params body ...)
         (unless (and (L? name) (symbol? (unL name)) (L? params) (list? (unL params)))
           (fail! (diag-at "ERR_MACRO" (loc->info "defmacro" (loc-of f))
                           #:message "usage: (defmacro name (params ...) body ...)"
                           #:suggestion "Check defmacro syntax")))
         (define pname (unL name))
         (define ps (map (lambda (p)
                           (unless (symbol? (unL p))
                             (fail! (diag-at "ERR_MACRO" (loc->info "defmacro" (loc-of p))
                                             #:message "macro parameters must be symbols")))
                           (unL p))
                         (unL params)))
         (define body-d (map L->datum body))
         (when (hash-has-key? macs pname)
           (fail! (diag-at "ERR_MACRO" (loc->info (format "defmacro:~a" pname) (loc-of f))
                           #:message (format "duplicate macro ~a" pname)
                           #:suggestion "Remove the earlier defmacro")))
         (define proc
           (with-handlers ([exn:lcir? (lambda (e) (raise e))]
                           [exn:fail? (lambda (e)
                                        (fail! (diag-at "ERR_MACRO"
                                                        (loc->info (format "defmacro:~a" pname) (loc-of f))
                                                        #:message (exn-message e)
                                                        #:suggestion "Fix the macro body")))])
             (eval `(lambda ,ps ,@body-d) meta-namespace)))
         (set! macs (hash-set macs pname proc))]
        [_ (fail! (diag-at "ERR_MACRO" (loc->info "defmacro" (loc-of f))
                           #:message "bad defmacro"
                           #:suggestion "usage: (defmacro name (params ...) body ...)"))])))
  (current-macros macs)
  macs)

(define (call-macro name proc args loc)
  (when (>= (macro-depth) 200)
    (fail! (diag-at "ERR_MACRO" (loc->info (format "macro:~a" name) loc)
                    #:message "macro expansion exceeded 200 iterations"
                    #:suggestion "A macro is expanding into itself")))
  (define result
    (parameterize ([macro-depth (add1 (macro-depth))])
      (with-handlers ([exn:lcir? (lambda (e) (raise e))]
                      [exn:fail? (lambda (e)
                                   (fail! (diag-at "ERR_MACRO"
                                                   (loc->info (format "macro:~a" name) loc)
                                                   #:message (exn-message e)
                                                   #:suggestion "Fix the macro invocation")))])
        (apply proc args))))
  (datum->L loc (normalize-datum result)))

(define (normalize-datum d)
  (cond
    [(keyword? d) (string->symbol (string-append ":" (keyword->string d)))]
    [(list? d) (map normalize-datum d)]
    [else d]))

(define (const-int lx what loc)
  (define d (unL lx))
  (unless (exact-integer? d)
    (fail! (diag-at "ERR_MACRO" (loc->info what loc)
                    #:message (format "~a expects a constant integer, got ~a" what (L->datum lx))
                    #:suggestion "Use a literal or a parameter that expands to an integer")))
  d)

(define numeric-ops
  (hash '+ +
        '- -
        '* *
        '= (lambda args (if (apply = args) 1 0))
        '< (lambda args (if (apply < args) 1 0))
        '> (lambda args (if (apply > args) 1 0))
        '<= (lambda args (if (apply <= args) 1 0))
        '>= (lambda args (if (apply >= args) 1 0))
        '== (lambda args (if (apply = args) 1 0))
        '!= (lambda args (if (apply = args) 0 1))
        'max max
        'min min))

(define (all-ints? xs)
  (andmap (lambda (x) (exact-integer? (unL x))) xs))

(define (unwrap-quote d)
  (if (and (list? d) (= (length d) 2) (eq? (car d) 'quote))
      (cadr d)
      d))

(define (expand-symcat args env loc)
  (define parts
    (for/list ([a args])
      (unwrap-quote (L->datum (expand-one a env)))))
  (L loc (apply symcat-parts parts)))

(define (expand-log name fn args env loc)
  (define xs (map (lambda (a) (expand-one a env)) args))
  (unless (all-ints? xs)
    (fail! (diag-at "ERR_MACRO" (loc->info (symbol->string name) loc)
                    #:message (format "~a expects constant integer arguments" name))))
  (L loc (apply fn (map unL xs))))

(define (expand-gen-for lx env)
  (define loc (loc-of lx))
  (define d (unL lx))
  (match d
    [(list _ (app unL (list var lo hi)) body ...)
     (define v (unL var))
     (unless (symbol? v)
       (fail! (diag-at "ERR_MACRO" (loc->info "gen-for" loc)
                       #:message "gen-for binder must be a symbol"
                       #:suggestion "Use (gen-for (i lo hi) body ...)")))
     (define lo-n (const-int (expand-one lo env) "gen-for" loc))
     (define hi-n (const-int (expand-one hi env) "gen-for" loc))
     (when (> (- hi-n lo-n) 100000)
       (fail! (diag-at "ERR_MACRO" (loc->info "gen-for" loc)
                       #:message (format "gen-for range ~a..~a is too large" lo-n hi-n))))
     (append-map
      (lambda (i)
        (define env2 (hash-set env v i))
        (append-map (lambda (b) (expand-splice b env2)) body))
      (range lo-n hi-n))]
    [_ (fail! (diag-at "ERR_MACRO" (loc->info "gen-for" loc)
                       #:message "usage: (gen-for (i lo hi) body ...)"
                       #:suggestion "Bounds are exclusive of hi"))]))

(define (balance op es loc)
  (match es
    ['() (fail! (diag-at "ERR_MACRO" (loc->info "reduce-tree" loc)
                         #:message "reduce-tree over an empty sequence"))]
    [(list e) e]
    [else
     (define mid (max 1 (quotient (add1 (length es)) 2)))
     (L loc (list (if (L? op) op (L loc op))
                  (balance op (take es mid) loc)
                  (balance op (drop es mid) loc)))]))

(define (expand-reduce lx env)
  (define loc (loc-of lx))
  (define d (unL lx))
  (match d
    [(list _ op (app unL (list var lo hi)) body)
     (define v (unL var))
     (unless (symbol? v)
       (fail! (diag-at "ERR_MACRO" (loc->info "reduce-tree" loc) #:message "bad binder")))
     (define lo-n (const-int (expand-one lo env) "reduce-tree" loc))
     (define hi-n (const-int (expand-one hi env) "reduce-tree" loc))
     (define es
       (for/list ([i (in-range lo-n hi-n)])
         (expand-one body (hash-set env v i))))
     (balance (expand-one op env) es loc)]
    [(list _ op e0 e1 es ...)
     (define op1 (expand-one op env))
     (define es1 (map (lambda (e) (expand-one e env)) (cons e0 (cons e1 es))))
     (balance op1 es1 loc)]
    [_ (fail! (diag-at "ERR_MACRO" (loc->info "reduce-tree" loc)
                       #:message "usage: (reduce-tree op (i lo hi) expr) or (reduce-tree op e0 e1 ...)"))]))

(define (expand-cat-for lx env)
  (define loc (loc-of lx))
  (define d (unL lx))
  (match d
    [(list _ (app unL (list var lo hi)) body)
     (define v (unL var))
     (unless (symbol? v)
       (fail! (diag-at "ERR_MACRO" (loc->info "cat-for" loc) #:message "bad binder")))
     (define lo-n (const-int (expand-one lo env) "cat-for" loc))
     (define hi-n (const-int (expand-one hi env) "cat-for" loc))
     (define es
       (for/list ([i (in-range lo-n hi-n)])
         (expand-one body (hash-set env v i))))
     (when (null? es)
       (fail! (diag-at "ERR_MACRO" (loc->info "cat-for" loc) #:message "empty cat-for")))
     (L loc (cons (L loc 'cat) es))]
    [_ (fail! (diag-at "ERR_MACRO" (loc->info "cat-for" loc)
                       #:message "usage: (cat-for (i lo hi) expr)"))]))

(define (fold-numeric head args loc)
  (define fn (hash-ref numeric-ops head #f))
  (and fn
       (all-ints? args)
       (let ([nums (map unL args)])
         (cond
           [(and (eq? head '-) (= (length nums) 1))
            (L loc (- (car nums)))]
           [(and (memq head '(= < > <= >= == != max min)) (< (length nums) 2))
            #f]
           [(and (eq? head '-) (< (length nums) 1)) #f]
           [(and (memq head '(+ *)) (< (length nums) 2)) #f]
           [else
            (with-handlers ([exn:fail? (lambda (e)
                                         (fail! (diag-at "ERR_MACRO" (loc->info (symbol->string head) loc)
                                                         #:message (exn-message e))))])
              (L loc (apply fn nums)))]))))

(define (fold-not args loc)
  (cond
    [(and (= (length args) 1) (exact-integer? (unL (car args))))
     (L loc (if (zero? (unL (car args))) 1 0))]
    [else #f]))

(define (expand-if args env loc)
  (match args
    [(list c t e)
     (define c1 (expand-one c env))
     (define cv (unL c1))
     (cond
       [(or (eq? cv #t) (and (exact-integer? cv) (not (zero? cv))))
        (expand-one t env)]
       [(or (eq? cv #f) (equal? cv 0))
        (expand-one e env)]
       [else
        (L loc (list (L loc 'mux) c1 (expand-one t env) (expand-one e env)))])]
    [_ (fail! (diag-at "ERR_MACRO" (loc->info "if" loc)
                       #:message "usage: (if cond then else)"))]))

;; Returns a single L.
(define (expand-one lx env)
  (set! lx (if (L? lx) (rewrite-infix lx) lx))
  (cond
    [(not (L? lx)) (datum->L #f lx)]
    [else
     (define d (L-d lx))
     (define loc (L-loc lx))
     (cond
       [(symbol? d)
        (if (hash-has-key? env d)
            (L loc (hash-ref env d))
            lx)]
       [(not (list? d)) lx]
       [(null? d) lx]
       [(eq? (form-head lx) 'quote) lx]
       ;; Bodies wait for parameter substitution at instantiation.
       [(memq (form-head lx) '(defmodule defsystem)) lx]
       [(eq? (form-head lx) 'gen-for)
        (define parts (expand-gen-for lx env))
        (cond
          [(null? parts)
           (fail! (diag-at "ERR_MACRO" (loc->info "gen-for" loc)
                           #:message "gen-for in expression position produced nothing"))]
          [(null? (cdr parts)) (car parts)]
          [else
           (fail! (diag-at "ERR_MACRO" (loc->info "gen-for" loc)
                           #:message "gen-for in expression position produced multiple forms"
                           #:suggestion "Use gen-for where a sequence is expected (a body, :state, :comb, ...)"))])]
       [(eq? (form-head lx) 'cat-for) (expand-cat-for lx env)]
       [(eq? (form-head lx) 'reduce-tree) (expand-reduce lx env)]
       [(eq? (form-head lx) 'symcat) (expand-symcat (cdr d) env loc)]
       [(eq? (form-head lx) 'log2) (expand-log 'log2 log2-int (cdr d) env loc)]
       [(eq? (form-head lx) 'clog2) (expand-log 'clog2 clog2-int (cdr d) env loc)]
       [(eq? (form-head lx) 'if) (expand-if (cdr d) env loc)]
       [(hash-ref (current-macros) (form-head lx) #f)
        => (lambda (proc)
             ;; Macros receive raw argument datums.
             (define args (map L->datum (cdr d)))
             (define expanded (call-macro (form-head lx) proc args loc))
             (expand-one expanded env))]
       [else
        ;; Splice gen-for / begin in every element, so they unroll inside
        ;; :state, :comb, :body and other sequences.
        (define parts (append-map (lambda (el) (expand-splice el env)) d))
        (define head1 (if (null? parts) #f (car parts)))
        (define args1 (if (null? parts) '() (cdr parts)))
        (define folded
          (or (and (L? head1) (symbol? (unL head1)) (fold-numeric (unL head1) args1 loc))
              (and (L? head1) (eq? (unL head1) 'not) (fold-not args1 loc))
              (and (L? head1) (eq? (unL head1) '~) (fold-not args1 loc))))
        (or folded
            (L loc parts))])]))

;; Returns a list of L, splicing gen-for and begin.
(define (expand-splice lx env)
  (set! lx (if (L? lx) (rewrite-infix lx) lx))
  (cond
    [(and (L? lx) (eq? (form-head lx) 'gen-for))
     (expand-gen-for lx env)]
    [(and (L? lx) (eq? (form-head lx) 'begin))
     (append-map (lambda (b) (expand-splice b env)) (cdr (unL lx)))]
    [else
     (define one (expand-one lx env))
     (cond
       [(and (L? one) (eq? (form-head one) 'begin))
        (append-map (lambda (b) (expand-splice b env)) (cdr (unL one)))]
       [(and (L? one) (eq? (form-head one) 'gen-for))
        (expand-splice one env)]
       [else (list one)])]))

(define (expand-body items env)
  (append-map (lambda (it) (expand-splice it env)) items))

;; Substitute parameter symbols with literal values. Binders of gen-for,
;; let, and quote are respected.
(define (subst-params lx env)
  (cond
    [(not (L? lx)) lx]
    [else
     (define d (L-d lx))
     (define loc (L-loc lx))
     (cond
       [(symbol? d)
        (if (hash-has-key? env d) (L loc (hash-ref env d)) lx)]
       [(not (list? d)) lx]
       [(null? d) lx]
       [(eq? (form-head lx) 'quote) lx]
       [(eq? (form-head lx) 'gen-for)
        (match d
          [(list g spec body ...)
           (match (unL spec)
             [(list var lo hi)
              (define v (unL var))
              (define env2 (hash-remove env v))
              (L loc (cons (subst-params g env)
                           (cons (L (loc-of spec)
                                    (list var
                                          (subst-params lo env)
                                          (subst-params hi env)))
                                 (map (lambda (b) (subst-params b env2)) body))))]
             [_ (L loc (map (lambda (x) (subst-params x env)) d))])]
          [_ lx])]
       [(eq? (form-head lx) 'cat-for)
        (subst-binder-form lx env)]
       [(eq? (form-head lx) 'reduce-tree)
        (match d
          [(list op spec body)
           #:when (and (L? spec) (list? (unL spec)) (= (length (unL spec)) 3)
                       (symbol? (unL (car (unL spec)))))
           (define var (car (unL spec)))
           (define v (unL var))
           (define env2 (hash-remove env v))
           (L loc (list (subst-params op env)
                        (L (loc-of spec)
                           (list var
                                 (subst-params (cadr (unL spec)) env)
                                 (subst-params (caddr (unL spec)) env)))
                        (subst-params body env2)))]
          [_ (L loc (map (lambda (x) (subst-params x env)) d))])]
       [(memq (form-head lx) '(let))
        (subst-let lx env)]
       [else (L loc (map (lambda (x) (subst-params x env)) d))])]))

(define (subst-binder-form lx env)
  (define d (unL lx))
  (define loc (L-loc lx))
  (match d
    [(list h spec body ...)
     (match (unL spec)
       [(list var lo hi)
        (define v (unL var))
        (define env2 (hash-remove env v))
        (L loc (cons (subst-params h env)
                     (cons (L (loc-of spec)
                              (list var
                                    (subst-params lo env)
                                    (subst-params hi env)))
                           (map (lambda (b) (subst-params b env2)) body))))]
       [_ (L loc (map (lambda (x) (subst-params x env)) d))])]
    [_ lx]))

(define (subst-let lx env)
  (define d (unL lx))
  (define loc (L-loc lx))
  ;; (let ((v e) ...) body ...)
  (match d
    [(list h bindings body ...)
     (define-values (b2 env2)
       (for/fold ([bs '()] [env env]) ([b (unL bindings)])
         (match (unL b)
           [(list name expr)
            (define e2 (subst-params expr env))
            (define env3 (hash-remove env (unL name)))
            (values (append bs (list (L (loc-of b) (list name e2)))) env3)]
           [_ (values (append bs (list (subst-params b env))) env)])))
     (L loc (list* h (L (loc-of bindings) b2)
                   (map (lambda (b) (subst-params b env2)) body)))]
    [_ (L loc (map (lambda (x) (subst-params x env)) d))]))

(define (expand-file-forms forms)
  ;; returns a list of expanded top-level L forms, defmacro removed,
  ;; begin spliced, macros applied. Module bodies are NOT unrolled.
  (register-macros! forms)
  (append-map
   (lambda (f)
     (if (eq? (form-head f) 'defmacro)
         '()
         (expand-splice f (hash))))
   forms))

;; After param subst, fully expand a module body (a list of clause L's).
(define (template-sexps body params)
  (define env (make-immutable-hash params))
  (define substed (map (lambda (b) (subst-params b env)) body))
  (expand-body substed (hash)))
