#lang racket
;; Flatten a hierarchical NHIR module into one netlist. Instance paths
;; are joined with "__" so ESL and the loop detector share one namespace.

(require "ast.rkt" "types.rkt" "nhir.rkt")
(provide (struct-out flatnet)
         (struct-out freg)
         (struct-out fwire)
         (struct-out ftable)
         flatten-design
         zero-of)

;; Re-export a zero expression builder by requiring schedule's zero through
;; a local copy, to keep flatten independent of schedule's private helpers.
(define (zero-of ty info)
  (match ty
    [(or (ty-uint _) (ty-sint _) (ty-enum _ _)) (e-lit 0 ty info)]
    [(ty-bundle fs)
     (e-pack (map (lambda (f) (cons (car f) (zero-of (cdr f) info))) fs) ty info)]
    [(ty-vec n e) (e-vlit (build-list n (lambda (_) (zero-of e info))) ty info)]
    [_ (e-lit 0 (ty-uint 1) info)]))

(struct flatnet (regs wires tables sides) #:transparent)
(struct freg (name ty init reset-less? clock we next mode guards info) #:transparent)
(struct fwire (name ty expr port? info) #:transparent)
(struct ftable (name depth elem-ty latency clock wen waddr wdata ren raddr rdata info) #:transparent)

(define (gname pfx name)
  (if (or (not pfx) (equal? pfx ""))
      name
      (string->symbol (format "~a__~a" pfx name))))

(define (rewrite e nmap)
  (match e
    [(e-ref n t i) (e-ref (hash-ref nmap n n) t i)]
    [(e-child inst port t i)
     (e-ref (hash-ref nmap (cons inst port)
                      (lambda () (error 'flatten "unmapped ~a.~a" inst port)))
            t i)]
    [(e-tread n a t i)
     (e-tread (hash-ref nmap n) (rewrite a nmap) t i)]
    [(e-rdata n t i)
     (e-ref (hash-ref nmap (string->symbol (format "~a__rdata" n))) t i)]
    [else (expr-map-kids (lambda (k) (rewrite k nmap)) e)]))

(define (flatten-design top)
  (define regs '())
  (define wires '())
  (define tables '())
  (define sides '())
  (define (rec h pfx drivers)
    (define (g name) (gname pfx name))
    (define nmap (make-hash))
    (for ([p (hmod-ports h)])
      (hash-set! nmap (hport-name p) (g (hport-name p))))
    (for ([r (hmod-regs h)])
      (hash-set! nmap (hreg-name r) (g (hreg-name r))))
    (for ([w (hmod-wires h)])
      (hash-set! nmap (hwire-name w) (g (hwire-name w))))
    (for ([t (hmod-tables h)])
      (hash-set! nmap (htable-name t) (g (htable-name t)))
      (hash-set! nmap (string->symbol (format "~a__rdata" (htable-name t)))
                 (g (string->symbol (format "~a__rdata" (htable-name t))))))
    (for ([ins (hmod-insts h)])
      (define child (hinst-mod ins))
      (for ([p (hmod-ports child)])
        (hash-set! nmap (cons (hinst-name ins) (hport-name p))
                   (g (string->symbol (format "~a__~a" (hinst-name ins) (hport-name p)))))))
    (define (rw e) (rewrite e nmap))
    (define port-names (list->set (map hport-name (hmod-ports h))))
    (for ([p (hmod-ports h)] #:when (eq? (hport-dir p) 'in))
      (define drv (hash-ref drivers (hport-name p) (zero-of (hport-ty p) (hport-info p))))
      (set! wires (cons (fwire (g (hport-name p)) (hport-ty p) drv #t (hport-info p)) wires)))
    (for ([w (hmod-wires h)])
      (set! wires (cons (fwire (g (hwire-name w)) (hwire-ty w) (rw (hwire-expr w))
                               (set-member? port-names (hwire-name w))
                               (hwire-info w))
                        wires)))
    (for ([r (hmod-regs h)])
      (set! regs (cons (freg (g (hreg-name r)) (hreg-ty r) (hreg-init r) (hreg-reset-less? r)
                             (hreg-clock r) (rw (hreg-we r)) (rw (hreg-next r))
                             (hreg-mode r) (map rw (hreg-guards r)) (hreg-info r))
                       regs)))
    (for ([t (hmod-tables h)])
      (define rdata (and (= (htable-latency t) 1)
                         (g (string->symbol (format "~a__rdata" (htable-name t))))))
      (set! tables (cons (ftable (g (htable-name t)) (htable-depth t) (htable-elem-ty t)
                                 (htable-latency t) (htable-clock t)
                                 (rw (htable-wen t)) (rw (htable-waddr t)) (rw (htable-wdata t))
                                 (rw (htable-ren t)) (rw (htable-raddr t))
                                 rdata (htable-info t))
                         tables)))
    (for ([s (hmod-sides h)])
      (define data
        (match (hside-kind s)
          ['log
           (match-define (list level parts) (hside-data s))
           (list level
                 (map (lambda (p)
                        (if (eq? (car p) 'val) (list 'val (rw (cadr p))) p))
                      parts))]
          ['check
           (match-define (list expr msg) (hside-data s))
           (list (rw expr) msg)]
          ['finish #f]))
      (set! sides (cons (hside (rw (hside-guard s)) (hside-kind s) data (hside-info s)) sides)))
    (for ([ins (hmod-insts h)])
      (define child (hinst-mod ins))
      (define cpfx (if (equal? pfx "")
                       (symbol->string (hinst-name ins))
                       (format "~a__~a" pfx (hinst-name ins))))
      (define cdrivers
        (for/hash ([p (hmod-ports child)] #:when (eq? (hport-dir p) 'in))
          (define ex (hash-ref (hinst-connects ins) (hport-name p)
                               (zero-of (hport-ty p) (hport-info p))))
          (values (hport-name p) (rw ex))))
      (rec child cpfx cdrivers)))
  (rec top "" (hash))
  (flatnet (reverse regs) (reverse wires) (reverse tables) (reverse sides)))
