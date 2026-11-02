#lang racket
;; Backend registry. ESL and SystemVerilog are implemented; C++ and SMT
;; are intentional stubs so the pipeline has a single dispatch point.

(require "diag.rkt")
(provide backend-names emit-cpp emit-smt)

(define backend-names '(esl sv cpp smt))

(define (unsupported name)
  (fail! (diag-at "ERR_BACKEND" (info (symbol->string name) #f #f #f)
                  #:message (format "backend ~a is not implemented" name)
                  #:suggestion "Use the esl or sv backend")))

(define (emit-cpp design) (unsupported 'cpp))
(define (emit-smt design) (unsupported 'smt))
