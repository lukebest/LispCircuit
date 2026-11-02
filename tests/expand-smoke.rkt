#lang racket
(require rackunit
         "../lcir/reader.rkt"
         "../lcir/expand.rkt"
         "../lcir/diag.rkt")

(define (ex s)
  (parameterize ([current-macros (hash)]
                 [current-diags (box '())])
    (define forms (read-lcir-string s "smoke"))
    (map L->datum (expand-file-forms forms))))

(define (ex-body s params)
  (parameterize ([current-macros (hash)]
                 [current-diags (box '())])
    (define forms (read-lcir-string s "smoke"))
    (define expanded (expand-file-forms forms))
    (define mod (car expanded))
    (define d (unL mod))
    ;; (defmodule Name . rest)  — rest includes :params and body; tests pass body only
    (map L->datum (template-sexps (cddr d) params))))

(check-equal? (ex "(infix (a + b) & ~mask)")
              '((& (+ a b) (~ mask))))

(check-equal? (ex "(infix a + b * c)")
              '((+ a (* b c))))

(check-equal? (ex "(infix x || y && z)")
              '((or x (and y z))))

(check-equal?
 (ex "(gen-for (i 0 3) (wire (symcat 'w_ i) (uint 8) i))")
 '((wire w_0 (uint 8) 0)
   (wire w_1 (uint 8) 1)
   (wire w_2 (uint 8) 2)))

(check-equal?
 (ex "(cat-for (i 0 4) (idx v i))")
 '((cat (idx v 0) (idx v 1) (idx v 2) (idx v 3))))

(check-equal?
 (ex "(reduce-tree +w (i 0 4) (idx v i))")
 '((+w (+w (idx v 0) (idx v 1)) (+w (idx v 2) (idx v 3)))))

(check-equal? (ex "(uint (clog2 8))") '((uint 3)))
(check-equal? (ex "(uint (log2 8))") '((uint 3)))

(check-equal?
 (ex "(defmacro twice (x) `(* ,x 2)) (twice a) (twice 3)")
 '((* a 2) 6))

(check-equal?
 (ex-body "(defmacro regs (n)
             (gen-for 0 n (lambda (i) `(,(symcat 'r i) :type (uint 8) :init 0))))
           (defmodule M :state ((regs 2)))"
          '())
 '(:state (((r0 :type (uint 8) :init 0)
            (r1 :type (uint 8) :init 0)))))

;; Module body is not unrolled until template-sexps substitutes params.
(define held (ex "(defmodule M :params ((N 4)) :comb ((gen-for (i 0 N) (wire (symcat 'w_ i) (uint 8) i))))"))
(check-equal? (car (car held)) 'defmodule)
(check-true (let loop ([x held])
              (match x
                ['gen-for #t]
                [(? list? xs) (ormap loop xs)]
                [_ #f])))

(define unrolled
  (ex-body "(defmodule M :ports () :comb ((gen-for (i 0 N) (wire (symcat 'w_ i) (uint (clog2 N)) i))))"
           '((N . 2))))
(check-equal? unrolled
              '(:ports ()
                :comb ((wire w_0 (uint 1) 0)
                       (wire w_1 (uint 1) 1))))

(printf "expand-smoke ok\n")
