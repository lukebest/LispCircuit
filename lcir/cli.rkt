#lang racket
(require json
         "diag.rkt" "compile.rkt" "esl.rkt" "flatten.rkt" "sv.rkt" "sv-tb.rkt"
         "cpp.rkt" "smt.rkt" "nhir.rkt" "nodepath.rkt" "reader.rkt")

(define (usage)
  (string-join
   '("usage: lcir <command> <file.lcir> [options]"
     "  check  FILE [--diag json|text]"
     "  expand FILE"
     "  sim    FILE --cycles N [--top NAME] [--dump-vcd F] [--dump-fst F] [--diag json|text]"
     "  sv     FILE -o DIR [--top NAME] [--cycles N]"
     "  cpp    FILE -o DIR [--top NAME] [--cycles N]"
     "  smt    FILE [-o OUT.smt2] [--top NAME] [--depth K] [--run]"
     "  query  FILE [PATH | --at LINE:COL | --list] [--diag json|text]"
     "  patch  FILE PATH --with SEXP [-o OUT | --in-place] [--dry-run] [--diag json|text]")
   "\n"))

(define value-flags '("--diag" "--cycles" "--top" "--dump-vcd" "--dump-fst" "-o" "--with" "--at" "--depth"))

(define (positionals args)
  (let loop ([as args])
    (cond
      [(null? as) '()]
      [(member (car as) value-flags) (loop (if (pair? (cdr as)) (cddr as) '()))]
      [(regexp-match? #rx"^-" (car as)) (loop (cdr as))]
      [else (cons (car as) (loop (cdr as)))])))

(define (has? args key) (and (member key args) #t))

;; Node paths for diagnostics. `text-overrides` maps a file name to text that
;; is not on disk yet (a patch candidate).
(define text-overrides (make-hash))
(define (node-path-fn)
  (lambda (file line col)
    (define text (hash-ref text-overrides file #f))
    (if text
        (with-handlers ([(lambda (_) #t) (lambda (_) #f)])
          (define pos (let loop ([i 0] [l 1])
                        (cond [(= l line) (+ i col 1)]
                              [(>= i (string-length text)) #f]
                              [(char=? (string-ref text i) #\newline) (loop (add1 i) (add1 l))]
                              [else (loop (add1 i) l)])))
          (and pos (path-at (read-nodes text file) pos)))
        (path-at-file file line col))))

(define (emit-result mode h text-lines)
  (if (eq? mode 'json)
      (begin (write-json h) (newline))
      (for-each displayln text-lines)))

(define (node-info text n path)
  (hasheq 'path path 'line (nd-line n) 'col (add1 (nd-col n)) 'text (node-text text n)))

(define (resolve-or-fail forms path)
  (or (resolve-path forms path)
      (fail! (diag-at "ERR_UNDEFINED" (info path #f #f #f)
                      #:message (format "no node at path ~a" path)
                      #:suggestion "Run `lcir query FILE --list` to see addressable paths"))))

(define (run-query file rest mode)
  (define text (file->string file))
  (define forms (read-nodes text file))
  (define pos-args (cdr (positionals rest)))
  (cond
    [(has? rest "--list")
     (define ps (list-paths forms))
     (emit-result mode
                  (for/list ([p ps]) (hasheq 'path (car p) 'line (nd-line (cdr p))
                                             'col (add1 (nd-col (cdr p)))))
                  (for/list ([p ps]) (format "~a:~a  ~a" (nd-line (cdr p)) (add1 (nd-col (cdr p))) (car p))))]
    [else
     (define path
       (cond
         [(flag rest "--at")
          => (lambda (lc)
               (match (regexp-match #rx"^([0-9]+):([0-9]+)$" lc)
                 [(list _ l c)
                  (or ((node-path-fn) file (string->number l) (sub1 (string->number c)))
                      (fail! (diag-at "ERR_UNDEFINED" (info "query" #f #f #f)
                                      #:message (format "no node at ~a" lc))))]
                 [_ (fail! (diag-at "ERR_PARSE" (info "query" #f #f #f)
                                    #:message "--at expects LINE:COL"))]))]
         [(pair? pos-args) (car pos-args)]
         [else (fail! (diag-at "ERR_PARSE" (info "query" #f #f #f)
                               #:message "query needs PATH, --at LINE:COL or --list"))]))
     (define n (resolve-or-fail forms path))
     (emit-result mode (node-info text n path)
                  (list (format "~a  (~a:~a)" path (nd-line n) (add1 (nd-col n)))
                        (node-text text n)))]))

(define (run-patch file rest mode)
  (define text (file->string file))
  (define forms (read-nodes text file))
  (define pos-args (cdr (positionals rest)))
  (unless (pair? pos-args)
    (fail! (diag-at "ERR_PARSE" (info "patch" #f #f #f) #:message "patch needs PATH")))
  (define path (car pos-args))
  (define new (or (flag rest "--with")
                  (fail! (diag-at "ERR_PARSE" (info "patch" #f #f #f) #:message "patch needs --with SEXP"))))
  (define parsed (with-handlers ([exn:fail? (lambda (_) #f)]) (read-nodes new "--with")))
  (unless (and parsed (= (length parsed) 1))
    (fail! (diag-at "ERR_PARSE" (info "patch" #f #f #f)
                    #:message "--with must be exactly one S-expression")))
  (define n (resolve-or-fail forms path))
  (define new-text (splice text n new))
  (define out (cond [(has? rest "--in-place") file] [(flag rest "-o")] [else #f]))
  (hash-set! text-overrides file new-text)
  (compile-source new-text #:file file)
  (hash-remove! text-overrides file)
  (when (and out (not (has? rest "--dry-run")))
    (call-with-output-file out #:exists 'replace (lambda (o) (write-string new-text o))))
  (emit-result mode
               (hasheq 'status "ok" 'path path 'old (node-text text n) 'new new
                       'written (if (and out (not (has? rest "--dry-run"))) out (json-null)))
               (if (or (not out) (has? rest "--dry-run"))
                   (list new-text)
                   (list (format "ok: ~a patched, written to ~a" path out)))))

(define (flag args key [default #f])
  (define i (index-of args key))
  (if i (list-ref args (add1 i)) default))

(define (print-diags ds mode)
  (if (eq? mode 'json)
      (write-json (diags->jsexpr ds))
      (displayln (format-diags ds) (current-error-port))))

(define (run argv)
  (define args (vector->list argv))
  (when (or (null? args) (member (car args) '("-h" "--help" "help")))
    (displayln (usage))
    (exit 0))
  (define cmd (car args))
  (define rest (cdr args))
  (define pos (positionals rest))
  (define file (and (pair? pos) (car pos)))
  (define mode (string->symbol (flag rest "--diag" "text")))
  (define (guarded thunk)
    (parameterize ([current-node-path (node-path-fn)])
      (with-handlers ([exn:lcir?
                       (lambda (e)
                         (print-diags (exn:lcir-diags e) mode)
                         (exit 1))])
        (thunk))))
  (guarded
   (lambda ()
     (unless file
       (fail! (diag-at "ERR_PARSE" (info "cli" #f #f #f) #:message "missing input file")))
     (case (string->symbol cmd)
       [(check)
        (compile-file file)
        (displayln "ok")]
       [(expand)
        (define text (file->string file))
        (pretty-write (expand-source text #:file file))]
       [(sim)
        (define cycles (string->number (flag rest "--cycles" "100")))
        (define top (flag rest "--top" #f))
        (define vcd (flag rest "--dump-vcd" #f))
        (define fst (flag rest "--dump-fst" #f))
        (when fst
          (unless (find-executable-path "vcd2fst")
            (fail! (diag-at "ERR_BACKEND" (info "fst" #f #f #f)
                            #:message "vcd2fst is not installed"
                            #:suggestion "Install vcd2fst or use --dump-vcd"))))
        (define d (compile-file file))
        (define sys (design-system d (and top (string->symbol top))))
        (define flat (flatten-design sys))
        (define vcd-path (or vcd (and fst (path-replace-extension fst ".vcd"))))
        (define result (simulate flat #:cycles cycles #:top-name (symbol->string (hmod-name sys))
                                 #:vcd vcd-path #:emit displayln))
        (when (and fst vcd-path)
          (unless (system* (find-executable-path "vcd2fst") vcd-path fst)
            (fail! (diag-at "ERR_BACKEND" (info "fst" #f #f #f) #:message "vcd2fst failed"))))]
       [(sv)
        (define dir (flag rest "-o" #f))
        (define cycles (string->number (flag rest "--cycles" "100")))
        (unless dir
          (fail! (diag-at "ERR_PARSE" (info "sv" #f #f #f) #:message "sv requires -o DIR")))
        (make-directory* dir)
        (define d (compile-file file))
        (define mods (design-modules d))
        (define syss (design-systems d))
        (define all (append mods syss))
        (call-with-output-file (build-path dir "lcir_types.sv") #:exists 'replace
          (lambda (o) (displayln (emit-types all) o)))
        (for ([m mods])
          (call-with-output-file (build-path dir (format "~a.sv" (mod-sv-name m))) #:exists 'replace
            (lambda (o) (display (emit-sv-file m) o))))
        (for ([s syss])
          (call-with-output-file (build-path dir (format "tb_~a.sv" (sv-name (hmod-name s))))
                                 #:exists 'replace
            (lambda (o) (display (emit-tb s cycles) o))))
        (displayln dir)]
       [(cpp)
        (define dir (or (flag rest "-o" #f)
                        (fail! (diag-at "ERR_PARSE" (info "cpp" #f #f #f) #:message "cpp requires -o DIR"))))
        (define cycles (string->number (flag rest "--cycles" "100")))
        (define top (flag rest "--top" #f))
        (define sys (design-system (compile-file file) (and top (string->symbol top))))
        (define name (symbol->string (hmod-name sys)))
        (define src (emit-cpp-sim (flatten-design sys) #:cycles cycles #:top-name name))
        (make-directory* dir)
        (define out (build-path dir (format "~a.cpp" name)))
        (call-with-output-file out #:exists 'replace (lambda (o) (write-string src o)))
        (displayln (path->string out))]
       [(smt)
        (define out (flag rest "-o" #f))
        (define depth (string->number (flag rest "--depth" "20")))
        (define top (flag rest "--top" #f))
        (define d (compile-file file))
        ;; --top may name a module: its inputs become free variables per cycle.
        (define mod (and top (findf (lambda (m) (eq? (hmod-name m) (string->symbol top)))
                                    (design-modules d))))
        (define sys (or mod (design-system d (and top (string->symbol top)))))
        (define text (emit-smt-text (flatten-design sys) #:depth depth
                                    #:top-name (symbol->string (hmod-name sys))
                                    #:free-inputs (if mod (hmod-input-names mod) '())))
        (when out
          (call-with-output-file out #:exists 'replace (lambda (o) (write-string text o))))
        (cond
          [(has? rest "--run")
           (define res (run-z3 text))
           (emit-result mode res (smt-report-lines res))
           (unless (equal? (hash-ref res 'status) "pass") (exit 1))]
          [(not out) (display text)]
          [else (displayln out)])]
       [(query) (run-query file rest mode)]
       [(patch) (run-patch file rest mode)]
       [else
        (displayln (usage) (current-error-port))
        (exit 2)]))))

(module+ main
  (run (current-command-line-arguments)))
