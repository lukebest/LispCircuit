#lang racket
;; Unit tests for the LCIR pipeline. Equivalence against Verilator lives in equiv.rkt.

(require racket/runtime-path
         rackunit
         rackunit/text-ui
         "../lcir/diag.rkt"
         "../lcir/reader.rkt"
         "../lcir/expand.rkt"
         "../lcir/compile.rkt"
         "../lcir/esl.rkt"
         "../lcir/flatten.rkt"
         "../lcir/vcd.rkt"
         "../lcir/nhir.rkt"
         "../lcir/bits.rkt"
         "../lcir/types.rkt"
         "../lcir/ast.rkt")

(define (diags-of src)
  (parameterize ([current-diags (box '())])
    (with-handlers ([exn:lcir? exn:lcir-diags])
      (compile-source src #:file "t.lcir" #:prims? #f)
      '())))

(define (must src)
  (define ds (diags-of src))
  (unless (null? ds)
    (fail (format-diags ds)))
  (compile-source src #:file "t.lcir" #:prims? #f))

(define (logs src #:cycles [n 20])
  (define d (must src))
  (define sys (design-system d))
  (sim-result-logs (simulate (flatten-design sys) #:cycles n #:top-name "t")))

(define (one src)
  (define ds (diags-of src))
  (check-equal? (length ds) 1 src)
  (car ds))

(define-runtime-path examples-dir "../examples")

(define suite
  (test-suite "lcir"
    (test-case "infix and gen-for"
      (parameterize ([current-macros (hash)] [current-diags (box '())])
        (check-equal? (map L->datum (expand-file-forms (read-lcir-string "(infix (a + b) & ~mask)")))
                      '((& (+ a b) (~ mask))))
        (check-equal? (map L->datum (expand-file-forms (read-lcir-string "(reduce-tree + (i 0 3) i)")))
                      '((+ (+ 0 1) 2)))))

    (test-case "width mismatch diagnostic"
      (define d
        (one #<<EOF
(defmodule StreamingMAC
  :params ((AW 8) (BW 8) (ACCW 20))
  :ports ((in a (sint AW)) (in b (sint BW)) (in en (uint 1)) (out acc (sint ACCW)))
  :state ((acc_reg :type (sint ACCW) :init 0))
  :comb ((assign acc acc_reg))
  (defrule compute_mac :guard en :body ((set! acc_reg (*w a b)))))
EOF
))
      (check-equal? (diag-code d) "ERR_WIDTH_MISMATCH")
      (check-equal? (diag-location d) "module:StreamingMAC -> rule:compute_mac -> stmt:(set! acc_reg ...)")
      (check-equal? (diag-expected d) "(sint 20)")
      (check-equal? (diag-actual d) "(sint 16)")
      (check-equal? (diag-suggestion d) "Wrap expression with (sext <expr> 20)"))

    (test-case "sign mismatch"
      (define d
        (one #<<EOF
(defmodule M
  :ports ((in a (uint 8)) (out y (uint 8)))
  :comb ((assign y (as-uint a)))
  :state ((r :type (sint 8) :init 0))
  (defrule s :guard 1 :body ((set! r a))))
EOF
))
      (check-equal? (diag-code d) "ERR_SIGN_MISMATCH"))

    (test-case "undefined, match, index, algo"
      (check-equal? (diag-code (one "(defmodule M :ports ((out y (uint 8))) :comb ((assign y z)))"))
                    "ERR_UNDEFINED")
      (check-equal? (diag-code
                     (one "(defenum E (A B)) (defmodule M :state ((r :type E :init A)) :ports ((out y E)) :comb ((assign y r)) (defrule s :guard 1 :body ((set! r (match r (A B) (B A))))))"))
                    "ERR_MATCH_NO_DEFAULT")
      (check-equal? (diag-code
                     (one "(defmodule M :ports ((out y (uint 8))) :comb ((wire v (vec 2 (uint 8)) (vlit (u 8 1) (u 8 2))) (assign y (idx v 5))))"))
                    "ERR_INDEX_OOB")
      (check-equal? (diag-code
                     (one "(defmodule M :state ((r :type (uint 8) :init 0)) (defalgo bad ((a (uint 8))) (uint 8) (+ a r)) :ports ((out y (uint 8))) :comb ((assign y (bad 1))))"))
                    "ERR_ALGO_STATEFUL"))

    (test-case "write conflict and priority"
      (check-equal? (diag-code
                     (one "(defmodule M :ports ((in a (uint 1)) (in b (uint 1)) (out y (uint 8))) :state ((r :type (uint 8) :init 0)) :comb ((assign y r)) (defrule ra :guard a :body ((set! r 1))) (defrule rb :guard b :body ((set! r 2))))"))
                    "ERR_WRITE_CONFLICT")
      (check-equal? (logs #<<EOF
(defmodule M
  :ports ((in a (uint 1)) (in b (uint 1)) (out y (uint 8)))
  :state ((r :type (uint 8) :init 0))
  :comb ((assign y r))
  (defrule ra :priority 0 :guard a :body ((set! r 1)))
  (defrule rb :priority 1 :guard b :body ((set! r 2))))
(defsystem S
  :instances ((dut M))
  (defrule t :guard 1 :body ((drive dut.a 1) (drive dut.b 1) (log info "y" dut.y) (finish))))
EOF
)
                    '("[cyc 0] info y=0")))

    (test-case "old value: set then read sees the committed value"
      (check-equal?
       (logs #<<EOF
(defmodule Swap
  :ports ((out y (uint 8)) (out z (uint 8)))
  :state ((a :type (uint 8) :init 1) (b :type (uint 8) :init 2))
  :comb ((assign y a) (assign z b))
  (defrule s :guard 1 :body ((set! a b) (set! b a))))
(defsystem S
  :instances ((dut Swap))
  :state ((n :type (uint 2) :init 0))
  (defrule t :guard (< n 2) :body ((set! n (+ n 1)) (log info "y" dut.y "z" dut.z)))
  (defrule stop :guard (== n 2) :priority 0 :body ((finish))))
EOF
)
       '("[cyc 0] info y=1 z=2"
         "[cyc 1] info y=2 z=1")))

    (test-case "comb loop names the cycle"
      (define d
        (one "(defmodule Loop :ports ((in x (uint 1)) (out y (uint 1))) :comb ((wire a (uint 1) (and b x)) (wire b (uint 1) (and a x)) (assign y a)))"))
      (check-equal? (diag-code d) "ERR_COMB_LOOP")
      (check-not-false (member "a" (diag-loop d)))
      (check-not-false (member "b" (diag-loop d))))

    (test-case "vcd contains the register"
      (define d (must #<<EOF
(defmodule C :ports ((out y (uint 8))) :state ((c :type (uint 8) :init 0)) :comb ((assign y c)) (defrule i :guard 1 :body ((set! c (+ c 1)))))
(defsystem S :instances ((dut C)) (defrule t :guard 1 :body ((log info "y" dut.y) (finish))))
EOF
))
      (define path (make-temporary-file "lcir~a.vcd"))
      (simulate (flatten-design (design-system d)) #:cycles 2 #:vcd path #:top-name "S")
      (define text (file->string path))
      (check-true (regexp-match? #rx"c" text))
      (check-true (regexp-match? #rx"\\$enddefinitions" text))
      (delete-file path))

    (test-case "bits wrap and sext"
      (define u8 (ty-uint 8))
      (define s8 (ty-sint 8))
      (define info0 (info "t" #f #f #f))
      (check-equal? (eval-const (e-binop '+ (e-lit 200 u8 info0) (e-lit 100 u8 info0) u8 info0))
                    (bitwise-and (+ 200 100) 255))
      (check-equal? (eval-const (e-cast 'sext (e-lit -2 s8 info0) (ty-sint 16) info0))
                    -2)
      (check-equal? (eval-const (e-binop '*w (e-lit 3 s8 info0) (e-lit -2 s8 info0) (ty-sint 16) info0))
                    -6))

    (test-case "bundle, vec, enum round trip"
      (define d (must #<<EOF
(defenum Color (RED GREEN BLUE))
(defmodule M
  :ports ((out y (uint 8)) (out c Color))
  :state ((px :type (bundle (r (uint 8)) (g (uint 4))) :init (pack (r 3) (g 1)))
          (xs :type (vec 3 (uint 4)) :init (vlit (u 4 1) (u 4 2) (u 4 3)))
          (col :type Color :init GREEN))
  :comb ((assign y (field px r))
         (assign c col)
         (wire z (uint 4) (idx xs 1)))
  (defrule s :guard (== z 2) :body ((set! col BLUE))))
(defsystem S
  :instances ((dut M))
  :state ((n :type (uint 2) :init 0))
  (defrule t :guard (< n 2) :body ((set! n (+ n 1)) (log info "y" dut.y "c" dut.c)))
  (defrule stop :guard (== n 2) :priority 0 :body ((finish))))
EOF
))
      (define ls (sim-result-logs (simulate (flatten-design (design-system d)) #:cycles 5)))
      (check-equal? (car ls) "[cyc 0] info y=3 c=GREEN")
      (check-equal? (cadr ls) "[cyc 1] info y=3 c=BLUE"))

    (test-case "primitives and the stream-slice macro elaborate"
      (define d
        (parameterize ([current-diags (box '())])
          (compile-source #<<EOF
(stream-slice :forward Wrap 8)
(defsystem S
  :instances ((f sync-fifo :params ((W 8) (DEPTH 4)))
              (w Wrap)
              (e elastic-pipeline :params ((W 8) (N 3)))
              (a async-fifo))
  (defrule z :guard 1 :body ((finish))))
EOF
                          #:file "prims-user.lcir" #:prims? #t)))
      (check-eq? (hmod-name (design-system d)) 'S))

    (test-case "shipped examples elaborate"
      (for ([name '("counter" "streaming_mac" "fifo_counter" "fsm_enum" "sram_lat1" "stream_pipeline")])
        (check-pred design? (compile-file (build-path examples-dir (format "~a.lcir" name))))))))

(define failures (run-tests suite))
(unless (zero? failures)
  (exit 1))
(displayln "unit tests ok")
