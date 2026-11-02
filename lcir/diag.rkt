#lang racket
;; Structured diagnostics. Compile errors become diag values, never raw stacks.

(provide (struct-out diag)
         (struct-out exn:lcir)
         (struct-out info)
         (struct-out loc)
         current-diags
         current-node-path
         diag-add!
         fail!
         flush-diags!
         diag->jsexpr
         diags->jsexpr
         format-diag
         format-diags
         info-path-str
         loc->info)

(struct loc (file line col) #:transparent)

(struct info (path file line col) #:transparent)

(struct diag (code location suggestion expected actual message loop line col file)
  #:transparent)

(struct exn:lcir exn:fail (diags)
  #:transparent)

(define current-diags (make-parameter #f))

;; (file line col) -> path string or #f. Set by the CLI so diagnostics can
;; carry a machine-usable node path; see nodepath.rkt.
(define current-node-path (make-parameter (lambda (file line col) #f)))

(define (diag-node-path d)
  (and (diag-file d) (diag-line d) (diag-col d)
       ((current-node-path) (diag-file d) (diag-line d) (diag-col d))))

(define (info-path-str i)
  (cond
    [(info? i) (info-path i)]
    [(string? i) i]
    [else ""]))

(define (loc->info path l)
  (if (loc? l)
      (info path (loc-file l) (loc-line l) (loc-col l))
      (info (or path "") #f #f #f)))

(define (make d)
  d)

(define (diag-add! d)
  (define box* (current-diags))
  (if box*
      (set-box! box* (append (unbox box*) (list d)))
      (raise (exn:lcir (format-diag d) (current-continuation-marks) (list d)))))

(define (flush-diags!)
  (define box* (current-diags))
  (define ds (if box* (unbox box*) '()))
  (unless (null? ds)
    (when box* (set-box! box* '()))
    (raise (exn:lcir (format-diags ds) (current-continuation-marks) ds))))

(define (fail! d)
  (diag-add! d)
  (flush-diags!))

(define (diag->jsexpr d)
  (define h (make-hasheq))
  (hash-set! h 'error_code (diag-code d))
  (hash-set! h 'location (diag-location d))
  (hash-set! h 'fix_suggestion (or (diag-suggestion d) ""))
  (when (diag-expected d) (hash-set! h 'expected_type (diag-expected d)))
  (when (diag-actual d) (hash-set! h 'actual_type (diag-actual d)))
  (when (diag-message d) (hash-set! h 'message (diag-message d)))
  (when (diag-loop d) (hash-set! h 'loop (diag-loop d)))
  (when (diag-line d) (hash-set! h 'line (diag-line d)))
  (when (diag-col d) (hash-set! h 'col (add1 (diag-col d))))
  (when (diag-file d) (hash-set! h 'file (diag-file d)))
  (let ([np (diag-node-path d)]) (when np (hash-set! h 'node_path np)))
  h)

(define (diags->jsexpr ds)
  (map diag->jsexpr ds))

(define (format-diag d)
  (define lines
    (filter values
            (list
             (diag-code d)
             (format "  location: ~a" (diag-location d))
             (and (diag-expected d) (format "  expected: ~a" (diag-expected d)))
             (and (diag-actual d) (format "  actual: ~a" (diag-actual d)))
             (and (diag-message d) (format "  message: ~a" (diag-message d)))
             (and (diag-loop d) (format "  loop: ~a" (string-join (diag-loop d) " -> ")))
             (and (diag-suggestion d) (not (equal? (diag-suggestion d) ""))
                  (format "  fix: ~a" (diag-suggestion d)))
             (let ([np (diag-node-path d)]) (and np (format "  node: ~a" np)))
             (and (diag-file d)
                  (format "  at: ~a:~a:~a" (diag-file d) (or (diag-line d) "?") (if (diag-col d) (add1 (diag-col d)) "?"))))))
  (string-join lines "\n"))

(define (format-diags ds)
  (string-join (map format-diag ds) "\n\n"))

(define (diag-at code info
                 #:suggestion [suggestion ""]
                 #:expected [expected #f]
                 #:actual [actual #f]
                 #:message [message #f]
                 #:loop [loop #f])
  (define i (if (info? info) info (info (or info "") #f #f #f)))
  (diag code
        (info-path i)
        suggestion
        expected
        actual
        message
        loop
        (info-line i)
        (info-col i)
        (and (info-file i) (format "~a" (info-file i)))))
(provide diag-at)
