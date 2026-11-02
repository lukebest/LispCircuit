#lang racket
(require rackunit
         "../lcir/diag.rkt"
         "../lcir/reader.rkt"
         "../lcir/expand.rkt"
         "../lcir/parse.rkt"
         "../lcir/check-types.rkt")

(define (check-src src)
  (define diags (box '()))
  (parameterize ([current-diags diags]
                 [current-macros (hash)])
    (with-handlers ([exn:lcir? (lambda (e) (exn:lcir-diags e))])
      (define forms (read-lcir-string src "t.lcir"))
      (define expanded (expand-file-forms forms))
      (define mod (car expanded))
      (define d (unL mod))
      (define name (unL (cadr d)))
      (define body0 (cddr d))
      (define params (module-params body0))
      (define body (drop-params body0))
      (define env (make-immutable-hash params))
      (define substed (map (lambda (b) (subst-params b env)) body))
      (define full (expand-body substed (hash)))
      (define am (parse-module name 'module params full (hash) (hash) "t.lcir"
                               (format "module:~a" name)))
      (check-module am (hash) (hash))
      '())))

(define diags
  (check-src #<<EOF
(defmodule StreamingMAC
  :params ((AW 8) (BW 8) (ACCW 20))
  :ports ((in a (sint AW))
          (in b (sint BW))
          (in en (uint 1))
          (out acc (sint ACCW)))
  :state ((acc_reg :type (sint ACCW) :init 0))
  :comb ((assign acc acc_reg))
  (defrule compute_mac
    :guard en
    :body ((set! acc_reg (*w a b)))))
EOF
))

(define d (car diags))
(check-equal? (diag-code d) "ERR_WIDTH_MISMATCH")
(check-equal? (diag-location d) "module:StreamingMAC -> rule:compute_mac -> stmt:(set! acc_reg ...)")
(check-equal? (diag-expected d) "(sint 20)")
(check-equal? (diag-actual d) "(sint 16)")
(check-equal? (diag-suggestion d) "Wrap expression with (sext <expr> 20)")

(define ok
  (check-src #<<EOF
(defmodule StreamingMAC
  :params ((AW 8) (BW 8) (ACCW 20))
  :ports ((in a (sint AW))
          (in b (sint BW))
          (in en (uint 1))
          (out acc (sint ACCW)))
  :state ((acc_reg :type (sint ACCW) :init 0))
  :comb ((assign acc acc_reg))
  (defrule compute_mac
    :guard en
    :body ((let ((prod (*w a b)))
             (set! acc_reg (+ acc_reg (sext prod ACCW)))))))
EOF
))
(check-equal? ok '())

(printf "type-smoke ok\n")
