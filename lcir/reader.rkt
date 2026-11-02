#lang racket
;; S-expression reader with source locations, a readtable that treats
;; `|` as an operator, and the `(infix ...)` rewriter.

(require "diag.rkt")
(provide (struct-out L)
         read-lcir-port
         read-lcir-file
         read-lcir-string
         rewrite-infix
         L->datum
         datum->L
         unL
         form-head
         kw?
         kw-name
         loc-of
         atom?
         lcir-readtable)

(struct L (loc d) #:transparent)

(define (unL x)
  (if (L? x) (L-d x) x))

(define (loc-of x)
  (if (L? x) (L-loc x) #f))

(define (atom? x)
  (let ([d (unL x)])
    (or (symbol? d) (number? d) (string? d) (boolean? d) (keyword? d))))

(define (form-head x)
  (define d (unL x))
  (and (pair? d)
       (let ([h (unL (car d))])
         (and (symbol? h) h))))

(define (kw? x)
  (define d (unL x))
  (and (symbol? d)
       (let ([s (symbol->string d)])
         (and (> (string-length s) 0)
              (char=? (string-ref s 0) #\:)))))

(define (kw-name x)
  (string->symbol (substring (symbol->string (unL x)) 1)))

(define (L->datum x)
  (cond
    [(L? x)
     (define d (L-d x))
     (if (list? d) (map L->datum d) (norm-out d))]
    [(list? x) (map L->datum x)]
    [else (norm-out x)]))

(define (norm-out d)
  (if (keyword? d)
      (string->symbol (string-append ":" (keyword->string d)))
      d))

(define (datum->L loc d)
  (cond
    [(L? d) d]
    [(keyword? d) (L loc (norm-out d))]
    [(list? d) (L loc (map (lambda (x) (datum->L loc x)) d))]
    [else (L loc d)]))

(define (norm-atom a)
  (if (keyword? a)
      (string->symbol (string-append ":" (keyword->string a)))
      a))

(define (stx->L s)
  (define lp (list (syntax-source s) (syntax-line s) (syntax-column s) (syntax-position s) (syntax-span s)))
  (define l (loc (syntax-source s) (syntax-line s) (syntax-column s)))
  (define e (syntax-e s))
  (cond
    [(list? e) (L l (map stx->L e))]
    [(pair? e)
     (fail! (diag "ERR_PARSE" (format "~a" lp) "improper list" #f #f "dotted pairs are not allowed" #f
                  (syntax-line s) (syntax-column s) (and (syntax-source s) (format "~a" (syntax-source s)))))]
    [else (L l (norm-atom e))]))

(define (read-bar ch port src line col pos)
  (if (eqv? (peek-char port) #\|)
      (begin
        (read-char port)
        (datum->syntax #f (string->symbol "||") (list src line col pos 2)))
      (datum->syntax #f '\| (list src line col pos 1))))

(define lcir-readtable
  (make-readtable #f #\| 'terminating-macro read-bar))

(define (read-lcir-port in src)
  (port-count-lines! in)
  (parameterize ([current-readtable lcir-readtable])
    (let loop ()
      (define s
        (with-handlers ([exn:fail:read?
                         (lambda (e)
                           (define l (let ([ls (exn:fail:read-srclocs e)]) (and (pair? ls) (car ls))))
                           (fail! (diag "ERR_PARSE" "reader" "Check parentheses and string quotes"
                                        #f #f
                                        (regexp-replace #rx"^[^ ]*: read-syntax: " (exn-message e) "")
                                        #f
                                        (and l (srcloc-line l)) (and l (srcloc-column l))
                                        (and src (format "~a" src)))))])
          (read-syntax src in)))
      (if (eof-object? s)
          '()
          (cons (rewrite-infix (stx->L s)) (loop))))))

(define (read-lcir-file path)
  (call-with-input-file path
    (lambda (in) (read-lcir-port in path))))

(define (read-lcir-string str [src "input"])
  (read-lcir-port (open-input-string str) src))

;; -------------------- infix --------------------

(define binary-prec
  (hash '* 70
        '+ 60
        '- 60
        '<< 50
        '>> 50
        '& 40
        '^ 30
        '\| 20
        '== 15
        '!= 15
        '< 15
        '> 15
        '<= 15
        '>= 15
        '&& 10
        (string->symbol "||") 5))

(define (binop? s)
  (and (symbol? s) (hash-has-key? binary-prec s)))

(define (map-op s)
  (cond
    [(eq? s '&&) 'and]
    [(eq? s (string->symbol "||")) 'or]
    [else s]))

(define (split-tilde lx)
  (define d (unL lx))
  (cond
    [(and (symbol? d)
          (let ([s (symbol->string d)])
            (and (> (string-length s) 1)
                 (char=? (string-ref s 0) #\~))))
     (define s (symbol->string d))
     (list (L (loc-of lx) '~)
           (L (loc-of lx) (string->symbol (substring s 1))))]
    [else (list lx)]))

(define (group-has-infix? lx)
  (define d (unL lx))
  (and (pair? d)
       (not (binop? (unL (car d))))
       (not (eq? (unL (car d)) '~))
       (ormap (lambda (el)
                (define s (unL el))
                (or (binop? s)
                    (and (symbol? s)
                         (> (string-length (symbol->string s)) 1)
                         (char=? (string-ref (symbol->string s) 0) #\~))))
              d)))

(define (parse-infix-seq toks loc)
  (define exploded (append-map split-tilde toks))
  (define-values (e rest) (parse-expr exploded 0 loc))
  (unless (null? rest)
    (fail! (diag "ERR_PARSE"
                 (format-loc loc)
                 "Remove the extra tokens"
                 #f #f
                 (format "leftover tokens in infix: ~a" (L->datum rest))
                 #f (and (loc? loc) (loc-line loc)) (and (loc? loc) (loc-col loc))
                 (and (loc? loc) (loc-file loc) (format "~a" (loc-file loc))))))
  e)

(define (format-loc loc)
  (if (loc? loc)
      (format "~a:~a:~a" (or (loc-file loc) "") (or (loc-line loc) "?") (or (loc-col loc) "?"))
      "infix"))

(define (parse-expr toks minp loc)
  (define-values (lhs rest0) (parse-unary toks loc))
  (let loop ([lhs lhs] [toks rest0])
    (cond
      [(null? toks) (values lhs toks)]
      [else
       (define op (unL (car toks)))
       (define p (and (symbol? op) (hash-ref binary-prec op #f)))
       (if (and p (>= p minp))
           (let-values ([(rhs rest) (parse-expr (cdr toks) (add1 p) loc)])
             (loop (L loc (list (L loc (map-op op)) lhs rhs)) rest))
           (values lhs toks))])))

(define (parse-unary toks loc)
  (when (null? toks)
    (fail! (diag "ERR_PARSE" (format-loc loc) "Complete the infix expression"
                 #f #f "unexpected end of infix expression" #f
                 (and (loc? loc) (loc-line loc)) (and (loc? loc) (loc-col loc))
                 (and (loc? loc) (loc-file loc) (format "~a" (loc-file loc))))))
  (define t (car toks))
  (define s (unL t))
  (cond
    [(eq? s '~)
     (define-values (e rest) (parse-unary (cdr toks) loc))
     (values (L loc (list (L loc '~) e)) rest)]
    [(eq? s '-)
     ;; In a primary position, '-' is unary. Binary '-' is handled by parse-expr.
     (define-values (e rest) (parse-unary (cdr toks) loc))
     (values (L loc (list (L loc '-) e)) rest)]
    [else (values (primary t loc) (cdr toks))]))

(define (primary t loc)
  (cond
    [(group-has-infix? t) (parse-infix-seq (unL t) (or (loc-of t) loc))]
    [else (rewrite-infix t)]))

(define (rewrite-infix lx)
  (cond
    [(not (L? lx)) lx]
    [(eq? (form-head lx) 'infix)
     (parse-infix-seq (cdr (unL lx)) (loc-of lx))]
    [(list? (unL lx))
     (L (L-loc lx) (map rewrite-infix (unL lx)))]
    [else lx]))
