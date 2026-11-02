#lang racket
;; ESL log versus Verilator log for every shipped example.

(require racket/runtime-path
         racket/string
         "../lcir/compile.rkt"
         "../lcir/esl.rkt"
         "../lcir/flatten.rkt"
         "../lcir/sv.rkt"
         "../lcir/sv-tb.rkt"
         "../lcir/nhir.rkt")

(define-runtime-path examples-dir "../examples")
(define-runtime-path build-dir "../build/equiv")

(define examples
  '("counter" "streaming_mac" "fifo_counter" "fsm_enum" "sram_lat1" "stream_pipeline"))

(define cycles 20)

(define (log-lines text)
  (filter (lambda (ln) (regexp-match? #rx"^\\[cyc " ln))
          (string-split text "\n")))

(define (run-one name)
  (define src (build-path examples-dir (format "~a.lcir" name)))
  (define d (compile-file src))
  (define sys (car (design-systems d)))
  (define esl (sim-result-logs (simulate (flatten-design sys) #:cycles cycles
                                         #:top-name (symbol->string (hmod-name sys)))))
  (define dir (build-path build-dir name))
  (make-directory* dir)
  (call-with-output-file (build-path dir "lcir_types.sv") #:exists 'replace
    (lambda (o) (displayln (emit-types (append (design-modules d) (design-systems d))) o)))
  (for ([m (design-modules d)])
    (call-with-output-file (build-path dir (format "~a.sv" (mod-sv-name m))) #:exists 'replace
      (lambda (o) (display (emit-sv-file m) o))))
  (define tb-name (format "tb_~a" (sv-name (hmod-name sys))))
  (call-with-output-file (build-path dir (format "~a.sv" tb-name)) #:exists 'replace
    (lambda (o) (display (emit-tb sys cycles) o)))
  (define svs
    (map path->string
         (filter (lambda (p) (equal? (path-get-extension p) #".sv"))
                 (directory-list dir #:build? #t))))
  (define ver
    (parameterize ([current-directory dir])
      (apply system*/exit-code
             (find-executable-path "verilator")
             (append
              (list "--binary" "--timing" "-j" "0"
                    "--top-module" tb-name
                    "-o" "tb")
              (map file-name-from-path svs)))))
  (unless (zero? ver)
    (error 'equiv "~a: verilator failed" name))
  (define exe (build-path dir "obj_dir" "tb"))
  (define out (open-output-string))
  (define err (open-output-string))
  (parameterize ([current-output-port out]
                 [current-error-port err])
    (unless (zero? (system*/exit-code exe))
      (error 'equiv "~a: simulation failed\n~a" name (get-output-string err))))
  (define rtl (log-lines (get-output-string out)))
  (unless (equal? esl rtl)
    (error 'equiv "~a mismatch\nESL ~s\nRTL ~s" name esl rtl))
  (printf "~a match (~a lines)\n" name (length esl)))

(for-each run-one examples)
(displayln "equiv ok")
