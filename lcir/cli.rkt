#lang racket
(require json
         "diag.rkt" "compile.rkt" "esl.rkt" "flatten.rkt" "sv.rkt" "sv-tb.rkt"
         "backend.rkt" "nhir.rkt")

(define (usage)
  (string-join
   '("usage: lcir <command> <file.lcir> [options]"
     "  check  FILE [--diag json|text]"
     "  expand FILE"
     "  sim    FILE --cycles N [--top NAME] [--dump-vcd F] [--dump-fst F] [--diag json|text]"
     "  sv     FILE -o DIR [--top NAME] [--cycles N]"
     "  cpp    FILE"
     "  smt    FILE")
   "\n"))

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
  (define file (findf (lambda (a) (not (regexp-match? #rx"^-" a))) rest))
  (define mode (string->symbol (flag rest "--diag" "text")))
  (define (guarded thunk)
    (with-handlers ([exn:lcir?
                     (lambda (e)
                       (print-diags (exn:lcir-diags e) mode)
                       (exit 1))])
      (thunk)))
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
                                 #:vcd vcd-path))
        (for ([ln (sim-result-logs result)]) (displayln ln))
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
       [(cpp) (compile-file file) (emit-cpp #f)]
       [(smt) (compile-file file) (emit-smt #f)]
       [else
        (displayln (usage) (current-error-port))
        (exit 2)]))))

(module+ main
  (run (current-command-line-arguments)))
