#lang racket
;; query / patch through the CLI, as an agent would drive it.

(require racket/runtime-path json rackunit)

(define-runtime-path root "..")
(define cli (path->string (build-path root "lcir" "cli.rkt")))
(define racket-exe (find-executable-path "racket"))

(define (lcir . args)
  (define o (open-output-string))
  (define code
    (parameterize ([current-output-port o] [current-error-port o])
      (apply system*/exit-code racket-exe cli args)))
  (values code (get-output-string o)))

(define tmp (make-temporary-file "lcir-patch-~a" 'directory))
(define src (path->string (build-path tmp "counter.lcir")))
(copy-file (build-path root "examples" "counter.lcir") src)
(define original (file->string src))

(define-values (qc qo) (lcir "query" src "module:Counter/rule:inc/:body/0" "--diag" "json"))
(check-equal? qc 0)
(check-equal? (hash-ref (string->jsexpr qo) 'text) "(set! c (+ c 1))")

(define-values (ac ao) (lcir "query" src "--at" "9:20"))
(check-equal? ac 0)
(check-true (string-prefix? ao "module:Counter/rule:inc/:body/0/2"))

;; Rejected patch: width error, file untouched, diagnostic names the node.
(define-values (bc bo) (lcir "patch" src "module:Counter/rule:inc/:body/0"
                              "--with" "(set! c (+ c (u 4 2)))" "--in-place" "--diag" "json"))
(check-equal? bc 1)
(define bd (car (string->jsexpr bo)))
(check-equal? (hash-ref bd 'error_code) "ERR_WIDTH_MISMATCH")
(check-equal? (hash-ref bd 'node_path) "module:Counter/rule:inc/:body/0/2")
(check-equal? (file->string src) original)

;; Accepted patch: count by 2, comments kept, sim log changes.
(define-values (pc po) (lcir "patch" src "module:Counter/rule:inc/:body/0"
                              "--with" "(set! c (+ c 2))" "--in-place"))
(check-equal? pc 0 po)
(check-true (string-contains? (file->string src) ";; Minimal cycle-accurate counter"))
(define-values (sc so) (lcir "sim" src "--cycles" "8"))
(check-equal? sc 0)
(check-equal? (filter (lambda (l) (string-prefix? l "[cyc")) (string-split so "\n"))
              '("[cyc 0] info y=0" "[cyc 1] info y=2"))

(define-values (uc uo) (lcir "query" src "module:Nope"))
(check-equal? uc 1)
(check-true (string-contains? uo "ERR_UNDEFINED"))

(delete-directory/files tmp)
(displayln "patch smoke ok")
