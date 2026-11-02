#lang racket
;; Lower rules to per-resource write enables.
;; Conflicting writers are parallel when their guards are disjoint,
;; combined with a priority mux, or rejected.

(require racket/list
         "diag.rkt" "ast.rkt" "types.rkt" "nhir.rkt" "bits.rkt")
(provide schedule-module)

(struct wspec (guard expr prio cf? rule info) #:transparent)
(struct twspec (guard addr data prio cf? rule info) #:transparent)
(struct rspec (guard addr prio cf? rule info) #:transparent)

(define (zero-expr ty info)
  (match ty
    [(or (ty-uint _) (ty-sint _) (ty-enum _ _)) (e-lit 0 ty info)]
    [(ty-bundle fs)
     (define fields (map (lambda (f) (cons (car f) (zero-expr (cdr f) info))) fs))
     (e-pack fields ty info)]
    [(ty-vec n e)
     (e-vlit (build-list n (lambda (_) (zero-expr e info))) ty info)]
    [_ (e-lit 0 (ty-uint 1) info)]))

(define (const-eval e info what)
  (with-handlers ([exn:runtime?
                   (lambda (ex)
                     (fail! (diag-at "ERR_PARSE" info
                                     #:message (format "~a must be a constant (~a)" what (exn:runtime-text ex))
                                     #:suggestion "Initial values cannot read registers or tables")))])
    (eval-const e)))

(define (inline-wires e wenv seen)
  (match e
    [(e-ref n t i)
     (cond
       [(hash-ref wenv n #f)
        => (lambda (body)
             (if (set-member? seen n)
                 (raise 'lcir-cycle)
                 (inline-wires body wenv (set-add seen n))))]
       [else e])]
    [else (expr-map-kids (lambda (k) (inline-wires k wenv seen)) e)]))

(define (try-inline e wenv)
  (with-handlers ([(lambda (v) (eq? v 'lcir-cycle)) (lambda _ #f)])
    (inline-wires e wenv (set))))

(define (negate e)
  (match e
    [(e-unop 'not a _ _) a]
    [(e-binop '== a b t i) (e-binop '!= a b t i)]
    [(e-binop '!= a b t i) (e-binop '== a b t i)]
    [else (e-unop 'not e (ty-uint 1) (expr-info e))]))

(define (eq-conflict? g1 g2)
  (match* (g1 g2)
    [((e-binop '== a (e-lit v1 _ _) _ _) (e-binop '== b (e-lit v2 _ _) _ _))
     (and (expr-equal? a b) (not (equal? v1 v2)))]
    [((e-binop '== a (e-lit v1 _ _) _ _) (e-binop '== (e-lit v2 _ _) b _ _))
     (and (expr-equal? a b) (not (equal? v1 v2)))]
    [(_ _) #f]))

(define (struct-exclusive? g1 g2)
  (or (and (e-lit? g1) (zero? (e-lit-val g1)))
      (and (e-lit? g2) (zero? (e-lit-val g2)))
      (expr-equal? g1 (negate g2))
      (expr-equal? g2 (negate g1))
      (eq-conflict? g1 g2)))

(define (free-keys e)
  (define acc '())
  (define (add key ty)
    (unless (assoc key acc equal?)
      (set! acc (cons (list key ty) acc))))
  (expr-each
   (lambda (n)
     (match n
       [(e-ref name ty _) (add name ty)]
       [(e-child i p ty _) (add (list i p) ty)]
       [(or (e-tread _ _ _ _) (e-rdata _ _ _)) (raise 'lcir-giveup)]
       [_ (void)]))
   e)
  acc)

(define (assign-mask mask vars)
  (define env (hash))
  (define bit 0)
  (for ([v vars])
    (define ty (cadr v))
    (define w (ty-width ty))
    (define raw (bitwise-and (arithmetic-shift mask (- bit)) (sub1 (expt 2 w))))
    (define val (if (ty-sint? ty) (raw->signed raw w) raw))
    (set! env (hash-set env (car v) (cons val ty)))
    (set! bit (+ bit w)))
  env)

(define (plug e env)
  (match e
    [(e-ref n t i)
     (define cell (hash-ref env n #f))
     (if cell (e-lit (car cell) t i) e)]
    [(e-child i p t info)
     (define cell (hash-ref env (list i p) #f))
     (if cell (e-lit (car cell) t info) e)]
    [else (expr-map-kids (lambda (k) (plug k env)) e)]))

(define (enum-exclusive? g1 g2)
  (with-handlers ([(lambda (v) (eq? v 'lcir-giveup)) (lambda _ #f)]
                  [exn:runtime? (lambda _ #f)])
    (define vars
      (let ([all (append (free-keys g1) (free-keys g2))])
        (remove-duplicates all #:key car equal?)))
    (when (ormap (lambda (v) (not (ty-scalar? (cadr v)))) vars)
      (raise 'lcir-giveup))
    (define bits (apply + 0 (map (lambda (v) (ty-width (cadr v))) vars)))
    (when (> bits 20) (raise 'lcir-giveup))
    (for/and ([mask (in-range (expt 2 bits))])
      (define env (assign-mask mask vars))
      (define v1 (eval-const (plug g1 env)))
      (define v2 (eval-const (plug g2 env)))
      (not (and (= v1 1) (= v2 1))))))

(define (exclusive-guards? g1 g2 wenv)
  (define i1 (try-inline g1 wenv))
  (define i2 (try-inline g2 wenv))
  (and i1 i2
       (or (struct-exclusive? i1 i2)
           (enum-exclusive? i1 i2))))

(define (nest specs result-ty)
  (match specs
    [(list s) (wspec-expr s)]
    [(cons s r)
     (e-mux (wspec-guard s) (wspec-expr s) (nest r result-ty) result-ty (wspec-info s))]))

(define (choose-mode specs wenv what info)
  (cond
    [(andmap (lambda (p) (exclusive-guards? (wspec-guard (car p)) (wspec-guard (cadr p)) wenv))
             (combinations specs 2))
     'exclusive]
    [(andmap wspec-cf? specs) 'cf]
    [(andmap (lambda (s) (number? (wspec-prio s))) specs)
     (define ps (map wspec-prio specs))
     (unless (= (length ps) (set-count (list->set ps)))
       (fail! (diag-at "ERR_WRITE_CONFLICT" info
                       #:message (format "duplicate :priority among writers of ~a" what)
                       #:suggestion "Give each conflicting rule a distinct :priority")))
     'prio]
    [else
     (fail! (diag-at "ERR_WRITE_CONFLICT" info
                     #:message (format "rules ~a all write ~a and may fire together"
                                       (map wspec-rule specs) what)
                     #:suggestion "Set :priority (lower number wins) or :conflict-free t, or make the guards mutually exclusive"))]))

(define (order-specs specs mode)
  (if (eq? mode 'prio)
      (sort specs < #:key wspec-prio)
      specs))

(define (resolve-reg name ty init specs wenv info)
  (match specs
    ['() (values (e-lit 0 (ty-uint 1) info) (e-ref name ty info) 'none '())]
    [(list s) (values (wspec-guard s) (wspec-expr s) 'single (list (wspec-guard s)))]
    [else
     (define mode (choose-mode specs wenv name info))
     (define ordered (order-specs specs mode))
     (values (e-or (map wspec-guard ordered) info)
             (nest ordered ty)
             mode
             (map wspec-guard ordered))]))

(define (mux-exprs guards vals ty info)
  (match (map cons guards vals)
    [(list (cons _ v)) v]
    [(cons (cons g v) rest)
     (e-mux g v (mux-exprs (map car rest) (map cdr rest) ty info) ty info)]))

(define (resolve-write specs ty info wenv what)
  (define as-w
    (map (lambda (s)
           (wspec (twspec-guard s) (twspec-data s) (twspec-prio s) (twspec-cf? s)
                  (twspec-rule s) (twspec-info s)))
         specs))
  (match specs
    ['() (values (e-lit 0 (ty-uint 1) info)
                 (e-lit 0 (ty-uint 1) info)
                 (zero-expr ty info)
                 'none '())]
    [(list s) (values (twspec-guard s) (twspec-addr s) (twspec-data s) 'single (list (twspec-guard s)))]
    [else
     (define mode (choose-mode as-w wenv what info))
     (define ordered
       (if (eq? mode 'prio)
           (sort specs < #:key twspec-prio)
           specs))
     (define guards (map twspec-guard ordered))
     (values (e-or guards info)
             (mux-exprs guards (map twspec-addr ordered) (expr-ty (twspec-addr (car ordered))) info)
             (mux-exprs guards (map twspec-data ordered) ty info)
             mode
             guards)]))

(define (resolve-read specs info wenv what)
  (define as-w
    (map (lambda (s)
           (wspec (rspec-guard s) (rspec-addr s) (rspec-prio s) (rspec-cf? s)
                  (rspec-rule s) (rspec-info s)))
         specs))
  (match specs
    ['() (values (e-lit 0 (ty-uint 1) info) (e-lit 0 (ty-uint 1) info) 'none '())]
    [(list s) (values (rspec-guard s) (rspec-addr s) 'single (list (rspec-guard s)))]
    [else
     (define mode (choose-mode as-w wenv what info))
     (define ordered
       (if (eq? mode 'prio) (sort specs < #:key rspec-prio) specs))
     (define guards (map rspec-guard ordered))
     (values (e-or guards info)
             (mux-exprs guards (map rspec-addr ordered) (expr-ty (rspec-addr (car ordered))) info)
             mode
             guards)]))

(define (add-drive-regs m)
  (define drives '())
  (define (walk st)
    (match st
      [(st-drive inst port _ _) (set! drives (cons (cons inst port) drives))]
      [(st-let _ body _) (for-each walk body)]
      [_ (void)]))
  (for* ([r (amod-rules m)] [st (arule-body r)]) (walk st))
  (define specs (remove-duplicates drives))
  (define regs (amod-regs m))
  (define insts (amod-insts m))
  (define regmap (make-hash))
  (for ([d specs])
    (match-define (cons inst port) d)
    (define ins (findf (lambda (i) (eq? (ainst-name i) inst)) insts))
    (define p (hmod-port (ainst-mod ins) port))
    (define rname (string->symbol (format "drv__~a__~a" inst port)))
    (when (hash-has-key? (ainst-connects ins) port)
      (fail! (diag-at "ERR_PARSE" (ainst-info ins)
                      #:message (format "~a.~a is both assigned and driven" inst port))))
    (set! regs (append regs
                       (list (areg rname (hport-ty p) (zero-expr (hport-ty p) (hport-info p))
                                   #f (car (amod-clocks m)) (hport-info p)))))
    (hash-set! regmap d rname))
  (define (rw-stmt st)
    (match st
      [(st-drive inst port expr info)
       (st-set (hash-ref regmap (cons inst port)) expr info)]
      [(st-let bs body info) (st-let bs (map rw-stmt body) info)]
      [_ st]))
  (define rules
    (map (lambda (r) (struct-copy arule r [body (map rw-stmt (arule-body r))]))
         (amod-rules m)))
  (define insts2
    (for/list ([ins insts])
      (define cs (ainst-connects ins))
      (define cs2
        (for/fold ([cs cs]) ([d specs])
          (match-define (cons inst port) d)
          (if (eq? inst (ainst-name ins))
              (hash-set cs port (e-ref (hash-ref regmap d)
                                       (hport-ty (hmod-port (ainst-mod ins) port))
                                       (hport-info (hmod-port (ainst-mod ins) port))))
              cs)))
      (struct-copy ainst ins [connects cs2])))
  (struct-copy amod m [regs regs] [rules rules] [insts insts2]))

(define (fill-undriven m)
  (define insts
    (for/list ([ins (amod-insts m)])
      (define cs (ainst-connects ins))
      (define cs2
        (for/fold ([cs cs]) ([p (hmod-ports (ainst-mod ins))]
                             #:when (eq? (hport-dir p) 'in))
          (if (hash-has-key? cs (hport-name p))
              cs
              (if (eq? (amod-kind m) 'system)
                  (hash-set cs (hport-name p) (zero-expr (hport-ty p) (hport-info p)))
                  (begin
                    (fail! (diag-at "ERR_PARSE" (ainst-info ins)
                                    #:message (format "input ~a.~a is not driven" (ainst-name ins) (hport-name p))
                                    #:suggestion "Assign it in :comb, or drive it from the testbench"))
                    cs)))))
      (struct-copy ainst ins [connects cs2])))
  (for ([p (amod-ports m)] #:when (eq? (aport-dir p) 'out))
    (unless (findf (lambda (w) (eq? (awire-name w) (aport-name p))) (amod-wires m))
      (fail! (diag-at "ERR_PARSE" (aport-info p)
                      #:message (format "output ~a is not assigned" (aport-name p))
                      #:suggestion "Add (assign port expr) in :comb"))))
  (struct-copy amod m [insts insts]))

(define (count-treas m)
  (define counts (make-hash))
  (define (note e)
    (expr-each (lambda (n)
                 (when (e-tread? n)
                   (hash-update! counts (e-tread-tname n) add1 0)))
               e))
  (for ([w (amod-wires m)]) (note (awire-expr w)))
  (for ([r (amod-rules m)])
    (note (arule-guard r))
    (for ([st (arule-body r)])
      (match st
        [(st-set _ e _) (note e)]
        [(st-twrite _ a d _) (note a) (note d)]
        [(st-tread _ a _) (note a)]
        [(st-log _ parts _) (for ([p parts]) (when (eq? (car p) 'val) (note (cadr p))))]
        [(st-check e _ _) (note e)]
        [_ (void)])))
  (for ([(name n) (in-hash counts)])
    (when (> n 1)
      (fail! (diag-at "ERR_PARSE" (amod-info m)
                      #:message (format "table ~a has ~a read expressions; only one read port is available" name n)
                      #:suggestion "Read it once into a wire and use that wire")))))

(define (schedule-module m0)
  (define m (fill-undriven (add-drive-regs m0)))
  (count-treas m)
  (define wenv (for/hash ([w (amod-wires m)]) (values (awire-name w) (awire-expr w))))
  (define reg-w (make-hash))
  (define tw (make-hash))
  (define tr (make-hash))
  (define sides '())
  (define (add-reg name spec)
    (hash-update! reg-w name (lambda (old) (cons spec old)) '()))
  (define (walk-rule r st)
    (match st
      [(st-set reg expr info)
       (add-reg reg (wspec (arule-guard r) expr (arule-prio r) (arule-cf? r) (arule-name r) info))]
      [(st-twrite tbl addr data info)
       (hash-update! tw tbl (lambda (old)
                              (cons (twspec (arule-guard r) addr data (arule-prio r) (arule-cf? r)
                                            (arule-name r) info)
                                    old))
                     '())]
      [(st-tread tbl addr info)
       (hash-update! tr tbl (lambda (old)
                              (cons (rspec (arule-guard r) addr (arule-prio r) (arule-cf? r)
                                           (arule-name r) info)
                                    old))
                     '())]
      [(st-log level parts info)
       (set! sides (cons (hside (arule-guard r) 'log (list level parts) info) sides))]
      [(st-check expr msg info)
       (set! sides (cons (hside (arule-guard r) 'check (list expr msg) info) sides))]
      [(st-finish info)
       (set! sides (cons (hside (arule-guard r) 'finish #f info) sides))]
      [(st-let _ body _) (for-each (lambda (s) (walk-rule r s)) body)]
      [(st-drive _ _ _ info)
       (fail! (diag-at "ERR_INTERNAL" info #:message "drive survived lowering"))]))
  (for ([r (amod-rules m)])
    (for ([st (arule-body r)]) (walk-rule r st)))
  (define clocks
    (remove-duplicates
     (append (amod-clocks m)
             (append-map (lambda (i) (hmod-clocks (ainst-mod i))) (amod-insts m)))))
  (define hregs
    (for/list ([r (amod-regs m)])
      (define specs (reverse (hash-ref reg-w (areg-name r) '())))
      (define info (areg-info r))
      (define init-v (const-eval (areg-init r) info (format "init of ~a" (areg-name r))))
      (define-values (we next mode guards)
        (resolve-reg (areg-name r) (areg-ty r) init-v specs wenv info))
      (hreg (areg-name r) (areg-ty r) init-v (areg-reset-less? r)
            (or (areg-clock r) (car clocks)) we next mode guards info)))
  (define htables
    (for/list ([t (amod-tables m)])
      (define info (atable-info t))
      (define-values (wen waddr wdata _mode _g)
        (resolve-write (reverse (hash-ref tw (atable-name t) '()))
                       (atable-elem-ty t) info wenv (atable-name t)))
      (define-values (ren raddr rmode rguards)
        (if (= (atable-latency t) 1)
            (resolve-read (reverse (hash-ref tr (atable-name t) '())) info wenv
                          (format "~a read" (atable-name t)))
            (values (e-lit 0 (ty-uint 1) info) (e-lit 0 (ty-uint 1) info) 'none '())))
      (htable (atable-name t) (atable-depth t) (atable-elem-ty t) (atable-latency t)
              (or (atable-clock t) (car clocks))
              wen waddr wdata ren raddr info)))
  (define hwires
    (for/list ([w (amod-wires m)])
      (hwire (awire-name w) (awire-ty w) (awire-expr w) (awire-info w))))
  (define hports
    (for/list ([p (amod-ports m)])
      (hport (aport-name p) (aport-dir p) (aport-ty p) (aport-info p))))
  (define hinsts
    (for/list ([i (amod-insts m)])
      (hinst (ainst-name i) (ainst-mod i) (ainst-connects i) (ainst-info i))))
  (hmod (amod-name m) (amod-kind m) (amod-params m) clocks hports (amod-aliases m)
        hregs hwires htables hinsts (reverse sides) (amod-info m)))
