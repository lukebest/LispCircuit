#lang racket
;; Node paths over raw source S-expressions, for AI agents.
;;
;; A path is "/"-separated segments, resolved from the list of top-level forms:
;;   module:X system:X enum:X macro:X   top-level definitions
;;   rule:X algo:X                      defrule / defalgo inside a module
;;   state:X table:X inst:X             entries of :state / :tables / :instances
;;   port:X wire:X                      entries of :ports / :comb (wire X ...)
;;   :kw                                the value following keyword :kw
;;   N                                  the N-th element (0-based)
;; Paths address source text before macro expansion, so a patch is a text
;; splice that keeps comments and formatting elsewhere.

(require "diag.rkt" "reader.rkt")
(provide (struct-out nd)
         read-nodes
         resolve-path
         path-at
         path-at-file
         list-paths
         node-text
         splice)

;; datum: symbol/number/string/... for atoms, #f for lists. kids: list of nd.
(struct nd (datum kids pos span line col) #:transparent)

(define (stx->nd s)
  (define e (syntax-e s))
  (define (mk d kids)
    (nd d kids (syntax-position s) (syntax-span s) (syntax-line s) (syntax-column s)))
  (cond
    [(list? e) (mk #f (map stx->nd e))]
    [(pair? e) (mk #f '())]
    [else (mk e #f)]))

(define (read-nodes text [src "input"])
  (define in (open-input-string text))
  (port-count-lines! in)
  (parameterize ([current-readtable lcir-readtable])
    (let loop ()
      (define s (read-syntax src in))
      (if (eof-object? s) '() (cons (stx->nd s) (loop))))))

(define (node-text text n)
  (substring text (sub1 (nd-pos n)) (+ (sub1 (nd-pos n)) (nd-span n))))

(define (splice text n new)
  (string-append (substring text 0 (sub1 (nd-pos n)))
                 new
                 (substring text (+ (sub1 (nd-pos n)) (nd-span n)))))

;; ---------------------------------------------------------------- helpers

(define (sym n) (and n (symbol? (nd-datum n)) (nd-datum n)))
(define (head n) (and (nd-kids n) (pair? (nd-kids n)) (sym (car (nd-kids n)))))
(define (nth n i) (and (nd-kids n) (< i (length (nd-kids n))) (list-ref (nd-kids n) i)))
(define (kw-sym? s) (and s (regexp-match? #rx"^:." (symbol->string s))))

(define (kw-value n kw)
  (let loop ([ks (or (nd-kids n) '())])
    (cond
      [(or (null? ks) (null? (cdr ks))) #f]
      [(eq? (sym (car ks)) kw) (cadr ks)]
      [else (loop (cdr ks))])))

(define top-kinds '((module . defmodule) (system . defsystem) (enum . defenum) (macro . defmacro)))
(define inner-kinds '((rule . defrule) (algo . defalgo)))
;; kind -> (keyword . position of the name inside an entry)
(define entry-kinds '((state :state 0) (table :tables 0) (inst :instances 0)
                      (port :ports 1) (wire :comb 1)))

(define (named-form? n def name)
  (and (eq? (head n) def) (equal? (symbol->string (or (sym (nth n 1)) '||)) name)))

(define (step n seg)
  (define m (regexp-match #rx"^([a-z]+):(.+)$" seg))
  (cond
    [(regexp-match? #rx"^[0-9]+$" seg) (nth n (string->number seg))]
    [(regexp-match? #rx"^:." seg) (kw-value n (string->symbol seg))]
    [(and m (assq (string->symbol (cadr m)) (append top-kinds inner-kinds)))
     => (lambda (p)
          (findf (lambda (k) (named-form? k (cdr p) (caddr m))) (or (nd-kids n) '())))]
    [(and m (assq (string->symbol (cadr m)) entry-kinds))
     => (lambda (p)
          (define lst (kw-value n (cadr p)))
          (and lst
               (findf (lambda (e)
                        (and (nd-kids e)
                             (or (not (eq? (car p) 'wire)) (eq? (head e) 'wire))
                             (let ([nm (sym (nth e (caddr p)))])
                               (and nm (equal? (symbol->string nm) (caddr m))))))
                      (or (nd-kids lst) '()))))]
    [else #f]))

(define (path-segments path)
  (filter (lambda (s) (not (equal? s ""))) (string-split path "/")))

;; Returns the node or #f.
(define (resolve-path forms path)
  (for/fold ([n (nd #f forms 1 0 1 0)]) ([seg (path-segments path)])
    (and n (step n seg))))

;; The segment that names child c (at index i) of parent p.
(define (segment-for p c i)
  (define (named alist)
    (for/or ([pr alist])
      (and (eq? (head c) (cdr pr)) (sym (nth c 1))
           (format "~a:~a" (car pr) (sym (nth c 1))))))
  (define kids (nd-kids p))
  (define kw-before (and (> i 0) (sym (list-ref kids (sub1 i)))))
  (or (named top-kinds)
      (named inner-kinds)
      (and (kw-sym? kw-before) (not (kw-sym? (sym c))) (symbol->string kw-before))
      (number->string i)))

(define (entry-segment p-kw c)
  (for/or ([ek entry-kinds])
    (and (eq? p-kw (cadr ek)) (nd-kids c)
         (or (not (eq? (car ek) 'wire)) (eq? (head c) 'wire))
         (sym (nth c (caddr ek)))
         (format "~a:~a" (car ek) (sym (nth c (caddr ek)))))))

(define (contains? n pos)
  (and (nd-pos n) (<= (nd-pos n) pos) (< pos (+ (nd-pos n) (nd-span n)))))

;; Innermost node containing character position pos (1-based); returns path or #f.
(define (path-at forms pos)
  (let loop ([p (nd #f forms 1 0 1 0)] [owner-kw #f] [acc '()])
    (define kids (or (nd-kids p) '()))
    (define hit (for/first ([c kids] [i (in-naturals)] #:when (contains? c pos)) (cons c i)))
    (cond
      [hit
       (define c (car hit))
       (define seg (or (and owner-kw (entry-segment owner-kw c))
                       (segment-for p c (cdr hit))))
       (define kw (and (regexp-match? #rx"^:" seg) (string->symbol seg)))
       (loop c kw (cons seg acc))]
      [(null? acc) #f]
      [else (string-join (reverse acc) "/")])))

(define (line-col->pos text line col)
  (let loop ([i 0] [l 1])
    (cond
      [(= l line) (+ i col 1)]
      [(>= i (string-length text)) #f]
      [(char=? (string-ref text i) #\newline) (loop (add1 i) (add1 l))]
      [else (loop (add1 i) l)])))

;; line is 1-based, col 0-based (Racket convention, as stored in diag).
(define (path-at-file file line col)
  (with-handlers ([(lambda (_) #t) (lambda (_) #f)])
    (define text (file->string file))
    (define pos (line-col->pos text line col))
    (and pos (path-at (read-nodes text file) pos))))

;; Every addressable named node: list of (path . node).
(define (list-paths forms)
  (define out '())
  (define (emit! path n) (set! out (cons (cons path n) out)))
  (let walk ([p (nd #f forms 1 0 1 0)] [prefix '()] [owner-kw #f])
    (for ([c (or (nd-kids p) '())] [i (in-naturals)])
      (define seg (or (and owner-kw (entry-segment owner-kw c))
                      (segment-for p c i)))
      (define path (append prefix (list seg)))
      (when (regexp-match? #rx"^[a-z]+:" seg)
        (emit! (string-join path "/") c)
        (walk c path #f))
      (when (and (regexp-match? #rx"^:" seg) (memq (string->symbol seg) '(:state :tables :instances :ports :comb)))
        (walk c path (string->symbol seg)))))
  (reverse out))
