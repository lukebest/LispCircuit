#lang racket
;; Read, expand, elaborate, typecheck, schedule, and reject comb loops.

(require racket/runtime-path
         "diag.rkt" "reader.rkt" "expand.rkt" "parse.rkt" "types.rkt"
         "check-types.rkt" "inline.rkt" "schedule.rkt" "flatten.rkt"
         "comb-loop.rkt" "nhir.rkt" "ast.rkt")
(provide (struct-out design)
         compile-source
         compile-file
         expand-source
         design-system
         prims-path)

(define-runtime-path prims-path "../lib/prims.lcir")

(struct design (enums modules systems) #:transparent)
(struct tmpl (name kind params body file lib? info) #:transparent)

(define (load-forms path)
  (expand-includes (read-lcir-file path) path))

(define (expand-includes forms path)
  (define base (or (and (path-string? path) (path-only path)) (current-directory)))
  (append-map
   (lambda (f)
     (if (eq? (form-head f) 'include)
         (let ([arg (unL (cadr (unL f)))])
           (unless (string? arg)
             (fail! (diag-at "ERR_PARSE" (loc->info "include" (loc-of f))
                             #:message "include expects a string path")))
           (load-forms (build-path base arg)))
         (list f)))
   forms))

(define (kind-of head)
  (case head
    [(defmodule) 'module]
    [(defsystem) 'system]
    [else #f]))

(define (compile-forms forms prim-file)
  (define expanded (expand-file-forms forms))
  (define enums (make-hash))
  (define templates (make-hash))
  (define algo-forms '())
  (for ([f expanded])
    (case (form-head f)
      [(defenum)
       (match (unL f)
         [(list _ name (app unL variants))
          (define nm (unL name))
          (define vs (map unL variants))
          (when (hash-has-key? enums nm)
            (fail! (diag-at "ERR_PARSE" (loc->info (format "enum:~a" nm) (loc-of f))
                            #:message (format "duplicate enum ~a" nm))))
          (unless (andmap symbol? vs)
            (fail! (diag-at "ERR_PARSE" (loc->info (format "enum:~a" nm) (loc-of f))
                            #:message "enum variants must be symbols")))
          (hash-set! enums nm (ty-enum nm vs))]
         [_ (fail! (diag-at "ERR_PARSE" (loc->info "defenum" (loc-of f))
                            #:message "usage: (defenum Name (V1 V2 ...))"))])]
      [(defmodule defsystem)
       (define d (unL f))
       (define nm (unL (cadr d)))
       (define body (cddr d))
       (define params (module-params body))
       (define lib? (and prim-file (equal? (and (loc? (loc-of f)) (loc-file (loc-of f))) prim-file)))
       (when (hash-has-key? templates nm)
         (fail! (diag-at "ERR_PARSE" (loc->info (format "module:~a" nm) (loc-of f))
                         #:message (format "duplicate module ~a" nm))))
       (hash-set! templates nm
                  (tmpl nm (kind-of (form-head f)) params (drop-params body)
                        (and (loc? (loc-of f)) (loc-file (loc-of f)))
                        lib?
                        (loc->info (format "module:~a" nm) (loc-of f))))]
      [(defalgo) (set! algo-forms (cons f algo-forms))]
      [(defmacro) (void)]
      [else
       (fail! (diag-at "ERR_PARSE" (loc->info "top" (loc-of f))
                       #:message (format "unknown top-level form ~a" (form-head f))))]))
  (define enum-hash (make-immutable-hash (hash->list enums)))
  (define parsed-algos
    (map (lambda (f)
           (parse-top-algo f enum-hash (format "algo:~a" (unL (cadr (unL f))))))
         (reverse algo-forms)))
  (define checked-algos (check-algos parsed-algos enum-hash))
  (define algo-hash
    (for/hash ([a checked-algos]) (values (aalgo-name a) a)))
  (define memo (make-hash))
  (define stack '())
  (define (elab name overrides)
    (define t (hash-ref templates name #f))
    (unless t
      (fail! (diag-at "ERR_UNDEFINED" (info (format "module:~a" name) #f #f #f)
                      #:message (format "unknown module ~a" name))))
    (define params
      (for/list ([p (tmpl-params t)])
        (cons (car p) (dict-ref overrides (car p) (cdr p)))))
    (for ([k (map car overrides)])
      (unless (dict-has-key? (tmpl-params t) k)
        (fail! (diag-at "ERR_PARSE" (tmpl-info t)
                        #:message (format "~a has no parameter ~a" name k)))))
    (define key (cons name params))
    (define hit (hash-ref memo key #f))
    (cond
      [(eq? hit 'pending)
       (fail! (diag-at "ERR_PARSE" (tmpl-info t)
                       #:message (format "recursive instantiation of ~a" name)))]
      [hit hit]
      [else
       (hash-set! memo key 'pending)
       (define env (make-immutable-hash params))
       (define substed (map (lambda (b) (subst-params b env)) (tmpl-body t)))
       (define full (expand-body substed (hash)))
       (define children
         (for/hash ([spec (module-instances full)])
           (match spec
             [(list iname mname overs)
              (values iname (elab mname overs))])))
       (define path (format "~a:~a" (if (eq? (tmpl-kind t) 'system) "system" "module") name))
       (define am (parse-module name (tmpl-kind t) params full enum-hash children
                                (or (tmpl-file t) "input") path))
       (define typed (check-module am enum-hash algo-hash))
       (define inlined (inline-module typed algo-hash))
       (define lifted (lift-module inlined))
       (define hm (schedule-module lifted))
       (check-loops! (flatten-design hm) (hmod-info hm))
       (hash-set! memo key hm)
       hm]))
  (define roots
    (for/list ([t (hash-values templates)] #:unless (tmpl-lib? t)) t))
  (for ([t roots])
    (elab (tmpl-name t) '()))
  (define systems
    (filter (lambda (h) (eq? (hmod-kind h) 'system))
            (filter hmod? (hash-values memo))))
  (define modules
    (filter (lambda (h) (eq? (hmod-kind h) 'module))
            (filter hmod? (hash-values memo))))
  (design (hash-values enums) modules systems))

(define (compile-source str #:file [file "input.lcir"] #:prims? [prims? #t])
  (parameterize ([current-diags (box '())]
                 [current-macros (hash)])
    (define user (expand-includes (read-lcir-port (open-input-string str) file) file))
    (define prims (if (and prims? (file-exists? prims-path)) (load-forms prims-path) '()))
    (compile-forms (append prims user) (and prims? prims-path))))

(define (compile-file path #:prims? [prims? #t])
  (parameterize ([current-diags (box '())]
                 [current-macros (hash)])
    (define user (load-forms path))
    (define prims (if (and prims? (file-exists? prims-path)) (load-forms prims-path) '()))
    (compile-forms (append prims user) (and prims? prims-path))))

(define (expand-source str #:file [file "input.lcir"] #:prims? [prims? #t])
  (parameterize ([current-diags (box '())]
                 [current-macros (hash)])
    (define user (read-lcir-port (open-input-string str) file))
    (define prims (if (and prims? (file-exists? prims-path)) (load-forms prims-path) '()))
    (define forms (expand-file-forms (append prims user)))
    ;; Elaborate module bodies at their default parameters so gen-for is visible.
    ;; Library primitives stay out of the listing; a macro they expand into
    ;; keeps the call-site location and is shown.
    (append-map
     (lambda (f)
       (define src (and (L? f) (loc? (loc-of f)) (loc-file (loc-of f))))
       (cond
         [(and prims? prims-path src (equal? src prims-path)) '()]
         [(memq (form-head f) '(defmodule defsystem))
          (define d (unL f))
          (define params (module-params (cddr d)))
          (define body (drop-params (cddr d)))
          (define full (expand-body (map (lambda (b) (subst-params b (make-immutable-hash params))) body) (hash)))
          (list (L->datum (L (loc-of f) (list* (car d) (cadr d) full))))]
         [(eq? (form-head f) 'defmacro) '()]
         [else (list (L->datum f))]))
     forms)))

(define (design-system d [name #f])
  (define syss (design-systems d))
  (cond
    [name
     (define s (findf (lambda (h) (eq? (hmod-name h) name)) syss))
     (unless s
       (fail! (diag-at "ERR_UNDEFINED" (info (format "system:~a" name) #f #f #f)
                       #:message (format "unknown system ~a" name))))
     s]
    [(null? syss)
     (fail! (diag-at "ERR_PARSE" (info "sim" #f #f #f)
                     #:message "no defsystem to simulate"
                     #:suggestion "Wrap the design in a defsystem"))]
    [(null? (cdr syss)) (car syss)]
    [else
     (fail! (diag-at "ERR_PARSE" (info "sim" #f #f #f)
                     #:message "multiple systems; pass --top"
                     #:suggestion (format "Choose one of ~a" (map hmod-name syss))))]))
