#lang racket
;; Parse expanded Core LCIR into an amod. Types of ports, regs and
;; wires are concrete; expression types are filled in by check-types.

(require "diag.rkt" "reader.rkt" "types.rkt" "ast.rkt" "nhir.rkt" "expand.rkt")
(provide parse-module
         parse-top-algo
         split-kw
         module-params
         module-instances
         drop-params)

(define current-enums (make-parameter (hash)))
(define current-insts (make-parameter (hash)))
(define current-aliases (make-parameter (hash)))
(define current-ports (make-parameter '()))
(define current-path (make-parameter ""))

(define (join-path a b)
  (cond
    [(or (not a) (equal? a "")) (or b "")]
    [(or (not b) (equal? b "")) a]
    [else (string-append a " -> " b)]))

(define (here lx [part #f])
  (loc->info (if part (join-path (current-path) part) (current-path))
             (and (L? lx) (L-loc lx))))

(define (failp code lx msg
               #:suggestion [suggestion ""]
               #:expected [expected #f]
               #:actual [actual #f])
  (fail! (diag-at code (here lx)
                  #:message msg
                  #:suggestion suggestion
                  #:expected expected
                  #:actual actual)))

(define (els lx who)
  (define d (unL lx))
  (unless (list? d)
    (failp "ERR_PARSE" lx (format "~a: expected a list" who)))
  d)

(define (as-sym lx who)
  (define d (unL lx))
  (unless (symbol? d)
    (failp "ERR_PARSE" lx (format "~a: expected a symbol" who)))
  d)

(define (as-int lx who)
  (define d (unL lx))
  (unless (exact-integer? d)
    (failp "ERR_PARSE" lx (format "~a: expected an integer, got ~a" who (L->datum lx))
           #:suggestion "Parameters and widths must be compile-time integers"))
  d)

(define (as-pos-width lx who)
  (define n (as-int lx who))
  (when (< n 1)
    (failp "ERR_PARSE" lx (format "~a: width must be >= 1" who)))
  n)

(define (as-bool lx who)
  (define d (unL lx))
  (cond
    [(eq? d #t) #t]
    [(eq? d #f) #f]
    [(eq? d 'true) #t]
    [(eq? d 'false) #f]
    [(eq? d 't) #t]
    [(eq? d 'nil) #f]
    [else (failp "ERR_PARSE" lx (format "~a: expected t or nil" who))]))

(define (sym+ a b)
  (string->symbol (string-append (symbol->string a) b)))

(define (split-kw items)
  (let loop ([items items] [h (hash)] [others '()])
    (cond
      [(null? items) (values h (reverse others))]
      [(kw? (car items))
       (when (null? (cdr items))
         (failp "ERR_PARSE" (car items) (format "missing value after ~a" (unL (car items)))))
       (define k (kw-name (car items)))
       (when (hash-has-key? h k)
         (failp "ERR_PARSE" (car items) (format "duplicate ~a" (unL (car items)))))
       (loop (cddr items) (hash-set h k (cadr items)) others)]
      [else (loop (cdr items) h (cons (car items) others))])))

(define (module-params body)
  (define-values (kw _) (split-kw body))
  (define p (hash-ref kw 'params #f))
  (if (not p)
      '()
      (for/list ([b (els p "params")])
        (match (els b "param")
          [(list n v)
           (define ev (expand-param v))
           (cons (as-sym n "param") (as-int ev "param default"))]
          [_ (failp "ERR_PARSE" b "parameter syntax is (Name default)")]))))

(define (expand-param v)
  (if (exact-integer? (unL v))
      v
      (expand-one v (hash))))

(define (module-instances body)
  (define-values (kw _) (split-kw body))
  (define p (hash-ref kw 'instances #f))
  (if (not p)
      '()
      (for/list ([b (els p "instances")])
        (define d (els b "instance"))
        (when (< (length d) 2)
          (failp "ERR_PARSE" b "instance syntax is (inst Module :params ((K V) ...))"))
        (define iname (as-sym (car d) "instance"))
        (define mname (as-sym (cadr d) "module"))
        (define-values (ikw _) (split-kw (cddr d)))
        (define pr (hash-ref ikw 'params #f))
        (define alist
          (if (not pr)
              '()
              (for/list ([x (els pr "params")])
                (match (els x "param override")
                  [(list n v) (cons (as-sym n "param") (as-int v "param override"))]
                  [_ (failp "ERR_PARSE" x "override syntax is (Name integer)")]))))
        (list iname mname alist))))

(define (drop-params body)
  (define-values (kw others) (split-kw body))
  (define keys '(ports state tables instances comb clocks))
  (append
   (append-map (lambda (k)
                 (if (hash-has-key? kw k)
                     (list (datum->L #f (string->symbol (format ":~a" k)))
                           (hash-ref kw k))
                     '()))
               keys)
   others))

(define (parse-type lx)
  (define d (unL lx))
  (cond
    [(symbol? d)
     (define en (hash-ref (current-enums) d #f))
     (unless en
       (failp "ERR_PARSE" lx (format "unknown type ~a" d)
              #:suggestion "Declare it with defenum, or use uint/sint/bundle/vec/stream"))
     en]
    [(list? d)
     (case (form-head lx)
       [(uint) (ty-uint (as-pos-width (cadr d) "uint"))]
       [(sint) (ty-sint (as-pos-width (cadr d) "sint"))]
       [(vec)
        (match d
          [(list _ n elem)
           (define len (as-int n "vec length"))
           (when (< len 1)
             (failp "ERR_PARSE" n "vec length must be >= 1"))
           (ty-vec len (parse-type elem))]
          [_ (failp "ERR_PARSE" lx "usage: (vec N T)")])]
       [(bundle)
        (ty-bundle
         (for/list ([f (cdr d)])
           (match (els f "bundle field")
             [(list fname ty)
              (cons (as-sym fname "field") (parse-type ty))]
             [_ (failp "ERR_PARSE" f "bundle field syntax is (name Type)")])))]
       [(stream)
        (match d
          [(list _ elem) (ty-stream (parse-type elem))]
          [_ (failp "ERR_PARSE" lx "usage: (stream T)")])]
       [else (failp "ERR_PARSE" lx (format "unknown type constructor ~a" (form-head lx)))])]
    [else (failp "ERR_PARSE" lx "bad type")]))

(define (expand-port dir name ty lx)
  (define info (here lx))
  (if (not (ty-stream? ty))
      (values (list (aport name dir ty info)) #f)
      (let* ([elem (ty-stream-elem ty)]
             [v (sym+ name "_valid")]
             [r (sym+ name "_ready")]
             [b (sym+ name "_bits")]
             ;; valid/bits follow the stream direction; ready is reversed.
             [vdir (if (eq? dir 'in) 'in 'out)]
             [rdir (if (eq? dir 'in) 'out 'in)])
        (values (list (aport v vdir (ty-uint 1) info)
                      (aport r rdir (ty-uint 1) info)
                      (aport b vdir elem info))
                (salias name elem dir v r b)))))

(define (parse-ports lx)
  (define items (if lx (els lx "ports") '()))
  (define ports '())
  (define aliases '())
  (define seen (set))
  (for ([p items])
    (match (els p "port")
      [(list dir name ty)
       (define d (unL dir))
       (unless (memq d '(in out))
         (failp "ERR_PARSE" dir "port direction must be in or out"))
       (define nm (as-sym name "port"))
       (define t (parse-type ty))
       (define-values (ps al) (expand-port d nm t p))
       (when (set-member? seen nm)
         (failp "ERR_PARSE" name (format "duplicate port ~a" nm)))
       (for ([sp ps])
         (when (set-member? seen (aport-name sp))
           (failp "ERR_PARSE" name (format "duplicate signal ~a" (aport-name sp))))
         (set! seen (set-add seen (aport-name sp)))
         (set! ports (append ports (list sp))))
       ;; Reserve the stream name itself so it cannot collide with a scalar port.
       (set! seen (set-add seen nm))
       (when al (set! aliases (append aliases (list al))))]
      [_ (failp "ERR_PARSE" p "port syntax is (in name Type) or (out name Type)")]))
  (values ports aliases))

(define (find-port name)
  (findf (lambda (p) (eq? (aport-name p) name)) (current-ports)))

(define (find-alias name)
  (hash-ref (current-aliases) name #f))

(define (dot-split sym)
  (define s (symbol->string sym))
  (define m (regexp-match-positions #rx"\\." s))
  (and m
       (cons (string->symbol (substring s 0 (caar m)))
             (string->symbol (substring s (cdar m))))))

(define (name-target sym lx)
  (define sp (dot-split sym))
  (cond
    [(not sp) (list 'local sym)]
    [else
     (define inst (car sp))
     (define port (cdr sp))
     (cond
       [(hash-has-key? (current-insts) inst) (list 'child inst port)]
       [(hash-has-key? (current-enums) inst)
        (failp "ERR_PARSE" lx (format "~a.~a is an enum literal, not a drive/assign target" inst port))]
       [else
        (failp "ERR_PARSE" lx (format "unknown instance ~a" inst)
               #:suggestion "Declare it in :instances")])]))

(define (stream-acc op arg lx)
  (unless (symbol? (unL arg))
    (failp "ERR_PARSE" arg "stream accessor expects a port name"))
  (define base (name-target (unL arg) arg))
  (define alias
    (match base
      [(list 'local name) (find-alias name)]
      [(list 'child inst name)
       (hmod-alias (hash-ref (current-insts) inst) name)]))
  (unless alias
    (failp "ERR_PARSE" lx (format "~a is not a stream port" (L->datum arg))
           #:suggestion "Use valid/ready/bits only on stream ports"))
  (define sig
    (case op
      [(valid) (salias-valid alias)]
      [(ready) (salias-ready alias)]
      [(bits) (salias-bits alias)]
      [else (failp "ERR_PARSE" lx "bad accessor")]))
  (match base
    [(list 'local _) (list 'local sig)]
    [(list 'child inst _) (list 'child inst sig)]))

(define (parse-target lx)
  (define h (form-head lx))
  (cond
    [(and (memq h '(valid ready)) (= (length (els lx "acc")) 2))
     (stream-acc h (cadr (els lx "acc")) lx)]
    [(and (eq? h 'bits) (= (length (els lx "acc")) 2))
     (stream-acc 'bits (cadr (els lx "acc")) lx)]
    [(symbol? (unL lx)) (name-target (unL lx) lx)]
    [else (failp "ERR_PARSE" lx "bad assign/drive target")]))

(define (signal-dir local? inst name)
  (cond
    [local?
     (define p (find-port name))
     (unless p
       (failp "ERR_PARSE" #f (format "unknown signal ~a" name)
              #:suggestion "Assign only to output ports or stream handshake signals"))
     (aport-dir p)]
    [else
     (define h (hash-ref (current-insts) inst))
     (define p (hmod-port h name))
     (unless p
       (failp "ERR_PARSE" #f (format "~a.~a is not a port" inst name)))
     (hport-dir p)]))

(define (signal-ty local? inst name)
  (if local?
      (aport-ty (find-port name))
      (hport-ty (hmod-port (hash-ref (current-insts) inst) name))))

(define (parse-atom sym lx)
  (define info (here lx))
  (define sp (dot-split sym))
  (cond
    [(not sp) (e-ref sym #f info)]
    [else
     (define a (car sp))
     (define b (cdr sp))
     (cond
       [(hash-has-key? (current-enums) a)
        (define en (hash-ref (current-enums) a))
        (define idx (index-of (ty-enum-variants en) b))
        (unless idx
          (failp "ERR_PARSE" lx (format "~a is not a variant of ~a" b a)))
        (e-lit idx en info)]
       [(hash-has-key? (current-insts) a)
        (e-child a b #f info)]
       [else
        (failp "ERR_PARSE" lx (format "unknown name ~a.~a" a b))])]))

(define (fold-bin op ps info)
  (let loop ([acc (car ps)] [r (cdr ps)])
    (if (null? r)
        acc
        (loop (e-binop op acc (car r) #f info) (cdr r)))))

(define (parse-let-expr bindings body)
  (define bs (els bindings "let"))
  (let loop ([bs bs])
    (cond
      [(null? bs) (parse-expr body)]
      [else
       (match (els (car bs) "binding")
         [(list nm ex)
          (e-let (as-sym nm "let") (parse-expr ex) (loop (cdr bs)) #f (here nm))]
         [_ (failp "ERR_PARSE" (car bs) "binding syntax is (name expr)")])])))

(define (parse-expr lx)
  (define d (unL lx))
  (define info (here lx))
  (cond
    [(exact-integer? d) (e-lit d (ty-int) info)]
    [(eq? d #t) (e-lit 1 (ty-uint 1) info)]
    [(eq? d #f) (e-lit 0 (ty-uint 1) info)]
    [(symbol? d) (parse-atom d lx)]
    [(not (list? d))
     (failp "ERR_PARSE" lx (format "bad expression ~a" (L->datum lx)))]
    [else
     (define h (form-head lx))
     (define args (cdr d))
     (case h
       [(let)
        (match d
          [(list _ bs body) (parse-let-expr bs body)]
          [_ (failp "ERR_PARSE" lx "usage: (let ((name expr) ...) body)")])]
       [(mux if)
        (match args
          [(list c t f) (e-mux (parse-expr c) (parse-expr t) (parse-expr f) #f info)]
          [_ (failp "ERR_PARSE" lx "usage: (mux cond then else)")])]
       [(match) (parse-match args info lx)]
       [(field)
        (match args
          [(list b f) (e-field (parse-expr b) (as-sym f "field") #f info)]
          [_ (failp "ERR_PARSE" lx "usage: (field expr field-name)")])]
       [(idx)
        (when (null? args) (failp "ERR_PARSE" lx "usage: (idx vec i ...)"))
        (for/fold ([base (parse-expr (car args))]) ([ix (cdr args)])
          (e-idx base (parse-expr ix) #f info))]
       [(valid ready)
        (match args
          [(list a) (sget h a info)]
          [_ (failp "ERR_PARSE" lx (format "usage: (~a stream)" h))])]
       [(bits)
        (match args
          [(list a) (sget 'bits a info)]
          [(list a hi lo)
           (define hv (as-int hi "bits"))
           (define lv (as-int lo "bits"))
           (when (or (< lv 0) (< hv lv))
             (failp "ERR_PARSE" lx "bits slice requires hi >= lo >= 0"))
           (e-slice (parse-expr a) hv lv (ty-uint (add1 (- hv lv))) info)]
          [_ (failp "ERR_PARSE" lx "usage: (bits stream) or (bits expr hi lo)")])]
       [(zext sext trunc)
        (match args
          [(list a w)
           (e-cast h (parse-expr a) (ty-uint (as-pos-width w (symbol->string h))) info)]
          [_ (failp "ERR_PARSE" lx (format "usage: (~a expr width)" h))])]
       [(as-uint as-sint)
        (match args
          [(list a) (e-cast h (parse-expr a) #f info)]
          [_ (failp "ERR_PARSE" lx (format "usage: (~a expr)" h))])]
       [(cat)
        (when (null? args) (failp "ERR_PARSE" lx "cat needs at least one expression"))
        (e-cat (map parse-expr args) #f info)]
       [(pack)
        (e-pack
         (for/list ([f args])
           (match (els f "pack")
             [(list fname ex) (cons (as-sym fname "field") (parse-expr ex))]
             [_ (failp "ERR_PARSE" f "pack field syntax is (name expr)")]))
         #f info)]
       [(vlit)
        (e-vlit (map parse-expr args) #f info)]
       [(u)
        (match args
          [(list w v)
           (define ww (as-pos-width w "u"))
           (define vv (as-int v "u"))
           (define t (ty-uint ww))
           (unless (fits-lit? vv t)
             (failp "ERR_WIDTH_MISMATCH" v (format "literal ~a does not fit (uint ~a)" vv ww)
                    #:expected (ty->string t) #:actual (format "~a" vv)
                    #:suggestion (format "Choose a wider uint or a smaller literal")))
           (e-lit vv t info)]
          [_ (failp "ERR_PARSE" lx "usage: (u width value)")])]
       [(s)
        (match args
          [(list w v)
           (define ww (as-pos-width w "s"))
           (define vv (as-int v "s"))
           (define t (ty-sint ww))
           (unless (fits-lit? vv t)
             (failp "ERR_WIDTH_MISMATCH" v (format "literal ~a does not fit (sint ~a)" vv ww)
                    #:expected (ty->string t) #:actual (format "~a" vv)))
           (e-lit vv t info)]
          [_ (failp "ERR_PARSE" lx "usage: (s width value)")])]
       [(table-read)
        (match args
          [(list t a) (e-tread (as-sym t "table") (parse-expr a) #f info)]
          [_ (failp "ERR_PARSE" lx "usage: (table-read tbl addr)")])]
       [(table-rdata)
        (match args
          [(list t) (e-rdata (as-sym t "table") #f info)]
          [_ (failp "ERR_PARSE" lx "usage: (table-rdata tbl)")])]
       [(+ - * & \| ^ and or +w -w *w == != < <= > >= << >>)
        (parse-op h args info lx)]
       [(~)
        (match args
          [(list a) (e-unop '~ (parse-expr a) #f info)]
          [_ (failp "ERR_PARSE" lx "usage: (~ expr)")])]
       [(not)
        (match args
          [(list a) (e-unop 'not (parse-expr a) (ty-uint 1) info)]
          [_ (failp "ERR_PARSE" lx "usage: (not expr)")])]
       [else
        (if (symbol? h)
            (e-call h (map parse-expr args) #f info)
            (failp "ERR_PARSE" lx "bad expression"))])]))

(define (sget op arg info)
  (define tgt (stream-acc op arg #f))
  (match tgt
    [(list 'local name) (e-ref name #f info)]
    [(list 'child inst name) (e-child inst name #f info)]))

(define (parse-op h args info lx)
  (cond
    [(and (eq? h '-) (= (length args) 1))
     (e-unop '- (parse-expr (car args)) #f info)]
    [(memq h '(== != < <= > >= << >> +w -w *w))
     (unless (= (length args) 2)
       (failp "ERR_PARSE" lx (format "~a expects 2 arguments" h)))
     (e-binop h (parse-expr (car args)) (parse-expr (cadr args)) #f info)]
    [(memq h '(+ - * & \| ^ and or))
     (when (< (length args) 2)
       (failp "ERR_PARSE" lx (format "~a expects at least 2 arguments" h)))
     (fold-bin h (map parse-expr args) info)]
    [else (failp "ERR_PARSE" lx "bad operator")]))

(define (parse-match args info lx)
  (when (null? args)
    (failp "ERR_PARSE" lx "usage: (match expr (pat body) ... (:default body))"))
  (define sel (parse-expr (car args)))
  (define-values (cases default)
    (for/fold ([cs '()] [def #f]) ([c (cdr args)])
      (define d (els c "match clause"))
      (cond
        [(eq? (unL (car d)) ':default)
         (when def (failp "ERR_PARSE" c "duplicate :default"))
         (unless (= (length d) 2) (failp "ERR_PARSE" c "usage: (:default expr)"))
         (values cs (parse-expr (cadr d)))]
        [else
         (unless (= (length d) 2) (failp "ERR_PARSE" c "usage: (pattern expr)"))
         (define pat (unL (car d)))
         (unless (or (symbol? pat) (exact-integer? pat))
           (failp "ERR_PARSE" c "match pattern must be an integer or a symbol"))
         (values (append cs (list (cons pat (parse-expr (cadr d))))) def)])))
  (e-match sel cases default #f info))

(define (stmt-sum lx)
  (define h (form-head lx))
  (cond
    [(and (eq? h 'set!) (>= (length (unL lx)) 2))
     (format "stmt:(set! ~a ...)" (L->datum (cadr (unL lx))))]
    [h (format "stmt:(~a ...)" h)]
    [else "stmt:(... )"]))

(define (parse-stmt lx)
  (parameterize ([current-path (join-path (current-path) (stmt-sum lx))])
    (define h (form-head lx))
    (define info (here lx))
    (define args (if (list? (unL lx)) (cdr (unL lx)) '()))
    (case h
      [(set!)
       (match args
         [(list name ex)
          (list (st-set (as-sym name "set!") (parse-expr ex) info))]
         [_ (failp "ERR_PARSE" lx "usage: (set! reg expr)")])]
      [(table-write)
       (match args
         [(list t a d)
          (list (st-twrite (as-sym t "table") (parse-expr a) (parse-expr d) info))]
         [_ (failp "ERR_PARSE" lx "usage: (table-write tbl addr data)")])]
      [(table-read)
       (match args
         [(list t a)
          (list (st-tread (as-sym t "table") (parse-expr a) info))]
         [_ (failp "ERR_PARSE" lx "usage: (table-read tbl addr)")])]
      [(drive)
       (match args
         [(list tgt ex)
          (match (parse-target tgt)
            [(list 'child inst port)
             (list (st-drive inst port (parse-expr ex) info))]
            [_ (failp "ERR_PARSE" tgt "drive only instance ports: (drive inst.port expr)")])]
         [_ (failp "ERR_PARSE" lx "usage: (drive inst.port expr)")])]
      [(log)
       (when (null? args) (failp "ERR_PARSE" lx "usage: (log level key expr ...)"))
       (define level0 (unL (car args)))
       (unless (or (symbol? level0) (string? level0))
         (failp "ERR_PARSE" (car args) "log level must be a symbol or string"))
       (define lv (if (symbol? level0) (symbol->string level0) level0))
       (define rest (cdr args))
       (unless (even? (length rest))
         (failp "ERR_PARSE" lx "log expects key/expr pairs"))
       (define parts
         (let loop ([xs rest])
           (if (null? xs)
               '()
               (let ([k (unL (car xs))])
                 (unless (or (string? k) (symbol? k))
                   (failp "ERR_PARSE" (car xs) "log key must be a string or symbol"))
                 (list* (list 'key (if (symbol? k) (symbol->string k) k))
                        (list 'val (parse-expr (cadr xs)))
                        (loop (cddr xs)))))))
       (list (st-log lv parts info))]
      [(check)
       (match args
         [(list ex msg)
          (unless (string? (unL msg))
            (failp "ERR_PARSE" msg "check message must be a string"))
          (list (st-check (parse-expr ex) (unL msg) info))]
         [_ (failp "ERR_PARSE" lx "usage: (check expr \"message\")")])]
      [(finish)
       (unless (null? args) (failp "ERR_PARSE" lx "usage: (finish)"))
       (list (st-finish info))]
      [(begin)
       (append-map parse-stmt args)]
      [(let)
       (match (unL lx)
         [(list _ bindings stmts ..1)
          (define bs
            (for/list ([b (els bindings "let")])
              (match (els b "binding")
                [(list nm ex) (list (as-sym nm "let") (parse-expr ex))]
                [_ (failp "ERR_PARSE" b "binding syntax is (name expr)")])))
          (list (st-let bs (append-map parse-stmt stmts) info))]
         [_ (failp "ERR_PARSE" lx "usage: (let ((name expr) ...) stmt ...)")])]
      [else (failp "ERR_PARSE" lx (format "unknown statement ~a" h))])))

(define (parse-stmt-list lx)
  (define d (unL lx))
  (unless (list? d) (failp "ERR_PARSE" lx "rule body must be a list of statements"))
  (cond
    [(null? d) '()]
    [(memq (form-head lx) '(set! let table-write table-read drive log check finish begin))
     (parse-stmt lx)]
    [else (append-map parse-stmt d)]))

(define (parse-rule lx)
  (define d (els lx "defrule"))
  (when (< (length d) 2)
    (failp "ERR_PARSE" lx "usage: (defrule name :guard expr :body (...))"))
  (define name (as-sym (cadr d) "rule"))
  (define-values (kw _) (split-kw (cddr d)))
  (define guard (hash-ref kw 'guard #f))
  (define body (hash-ref kw 'body #f))
  (unless guard (failp "ERR_PARSE" lx (format "rule ~a needs :guard" name)))
  (unless body (failp "ERR_PARSE" lx (format "rule ~a needs :body" name)))
  (define prio (hash-ref kw 'priority #f))
  (define cf (hash-ref kw 'conflict-free #f))
  (parameterize ([current-path (join-path (current-path) (format "rule:~a" name))])
    (arule name
           (if prio (as-int prio "priority") #f)
           (parse-expr guard)
           (parse-stmt-list body)
           (if cf (as-bool cf "conflict-free") #f)
           (here lx))))

(define (parse-algo lx)
  (match (els lx "defalgo")
    [(list _ name params ret body)
     (define nm (as-sym name "defalgo"))
     (define ps
       (for/list ([p (els params "params")])
         (match (els p "param")
           [(list pn ty) (cons (as-sym pn "param") (parse-type ty))]
           [_ (failp "ERR_PARSE" p "algo param syntax is (name Type)")])))
     (parameterize ([current-path (join-path (current-path) (format "algo:~a" nm))])
       (aalgo nm ps (parse-type ret) (parse-expr body) (here lx)))]
    [_ (failp "ERR_PARSE" lx "usage: (defalgo name ((p T) ...) Ret body)")]))

(define (parse-reg lx default-clock)
  (define d (els lx "state"))
  (when (null? d) (failp "ERR_PARSE" lx "empty state entry"))
  (define name (as-sym (car d) "reg"))
  (define-values (kw _) (split-kw (cdr d)))
  (define ty-l (hash-ref kw 'type #f))
  (define init-l (hash-ref kw 'init #f))
  (unless ty-l (failp "ERR_PARSE" lx (format "reg ~a needs :type" name)))
  (unless init-l (failp "ERR_PARSE" lx (format "reg ~a needs :init" name)))
  (define rl (hash-ref kw 'reset-less #f))
  (define clk (hash-ref kw 'clock #f))
  (parameterize ([current-path (join-path (current-path) (format "reg:~a" name))])
    (areg name
          (parse-type ty-l)
          (parse-expr init-l)
          (if rl (as-bool rl "reset-less") #f)
          (if clk (as-sym clk "clock") default-clock)
          (here lx))))

(define (parse-table lx default-clock)
  (define d (els lx "table"))
  (define name (as-sym (car d) "table"))
  (define-values (kw _) (split-kw (cdr d)))
  (define depth-l (hash-ref kw 'depth #f))
  (define ty-l (hash-ref kw 'type #f))
  (define lat-l (hash-ref kw 'latency #f))
  (define ports-l (hash-ref kw 'ports #f))
  (unless (and depth-l ty-l lat-l ports-l)
    (failp "ERR_PARSE" lx "table needs :depth :type :ports :latency"))
  (define depth (as-int depth-l "depth"))
  (when (< depth 1) (failp "ERR_PARSE" depth-l "table depth must be >= 1"))
  (define lat (as-int lat-l "latency"))
  (unless (memq lat '(0 1))
    (failp "ERR_PARSE" lat-l "latency must be 0 or 1"))
  (define-values (pkw _ports) (split-kw (els ports-l "ports")))
  (define nr (as-int (hash-ref pkw 'r (datum->L #f 0)) "r"))
  (define nw (as-int (hash-ref pkw 'w (datum->L #f 0)) "w"))
  (unless (and (= nr 1) (= nw 1))
    (failp "ERR_PARSE" ports-l "only :ports (:r 1 :w 1) is supported in this version"
           #:suggestion "Use a single read port and a single write port"))
  (define clk (hash-ref kw 'clock #f))
  (parameterize ([current-path (join-path (current-path) (format "table:~a" name))])
    (atable name depth (parse-type ty-l) lat
            (if clk (as-sym clk "clock") default-clock)
            (here lx))))

(define (parse-clocks lx)
  (if (not lx)
      '(clk)
      (let ([xs (map (lambda (s) (as-sym s "clock")) (els lx "clocks"))])
        (when (null? xs) (failp "ERR_PARSE" lx ":clocks must list at least one clock"))
        xs)))

(define (parse-top-algo lx enums path)
  (parameterize ([current-enums enums]
                 [current-insts (hash)]
                 [current-aliases (hash)]
                 [current-ports '()]
                 [current-path path])
    (parse-algo lx)))

(define (parse-module name kind params body enums children file path)
  (parameterize ([current-enums enums]
                 [current-insts children]
                 [current-path path])
    (define-values (kw others) (split-kw body))
    (define clocks (parse-clocks (hash-ref kw 'clocks #f)))
    (define default-clock (car clocks))
    (define-values (ports aliases) (parse-ports (hash-ref kw 'ports #f)))
    (parameterize ([current-ports ports]
                   [current-aliases
                    (for/hash ([a aliases]) (values (salias-name a) a))])
      (define regs
        (if (hash-ref kw 'state #f)
            (map (lambda (r) (parse-reg r default-clock)) (els (hash-ref kw 'state) "state"))
            '()))
      (define tables
        (if (hash-ref kw 'tables #f)
            (map (lambda (t) (parse-table t default-clock)) (els (hash-ref kw 'tables) "tables"))
            '()))
      (define specs (module-instances body))
      (define insts
        (for/list ([s specs])
          (match s
            [(list iname mname _)
             (define child (hash-ref children iname #f))
             (unless child
               (failp "ERR_PARSE" #f (format "internal: missing elaboration of ~a" iname)))
             (ainst iname child (hash) (here #f))])))
      (define connect (make-hash))
      (define wires '())
      (define wire-names (mutable-set))
      (define (add-wire! name ty expr lx)
        (when (set-member? wire-names name)
          (failp "ERR_PARSE" lx (format "duplicate driver for ~a" name)))
        (set-add! wire-names name)
        (set! wires (append wires (list (awire name ty expr (here lx (format "wire:~a" name)))))))
      (define (note-driver! tgt expr lx)
        (match tgt
          [(list 'local name)
           (define dir (signal-dir #t #f name))
           (unless (eq? dir 'out)
             (failp "ERR_PARSE" lx (format "cannot assign to input ~a" name)
                    #:suggestion "Inputs are driven by the parent. Assign outputs, or ready of an input stream."))
           (add-wire! name (signal-ty #t #f name) expr lx)]
          [(list 'child inst name)
           (define dir (signal-dir #f inst name))
           (unless (eq? dir 'in)
             (failp "ERR_PARSE" lx (format "cannot assign to ~a.~a (it is an output of the instance)" inst name)
                    #:suggestion "Read instance outputs. Drive only its inputs."))
           (define h (hash-ref! connect inst make-hash))
           (when (hash-has-key? h name)
             (failp "ERR_PARSE" lx (format "duplicate driver for ~a.~a" inst name)))
           (hash-set! h name expr)]))
      (when (hash-ref kw 'comb #f)
        (for ([c (els (hash-ref kw 'comb) "comb")])
          (case (form-head c)
            [(wire)
             (match (cdr (els c "wire"))
               [(list nm ty ex)
                (define name (as-sym nm "wire"))
                (define t (parse-type ty))
                (when (ty-stream? t)
                  (failp "ERR_PARSE" ty "wires cannot have stream type; use the stream's valid/ready/bits signals"))
                (add-wire! name t (parse-expr ex) c)]
               [_ (failp "ERR_PARSE" c "usage: (wire name Type expr)")])]
            [(assign)
             (match (cdr (els c "assign"))
               [(list tgt ex) (note-driver! (parse-target tgt) (parse-expr ex) c)]
               [_ (failp "ERR_PARSE" c "usage: (assign target expr)")])]
            [else (failp "ERR_PARSE" c "comb entries are (wire ...) or (assign ...)")])))
      (define rules '())
      (define algos '())
      (for ([o others])
        (case (form-head o)
          [(defrule) (set! rules (append rules (list (parse-rule o))))]
          [(defalgo) (set! algos (append algos (list (parse-algo o))))]
          [(defmodule defsystem defenum defmacro)
           (failp "ERR_PARSE" o (format "~a is only allowed at the top level" (form-head o)))]
          [else
           (failp "ERR_PARSE" o (format "unknown module clause ~a" (or (form-head o) (L->datum o)))
                  #:suggestion "Expected defrule, defalgo, or a :ports/:state/:comb section")]))
      (define insts2
        (for/list ([ins insts])
          (struct-copy ainst ins
                       [connects (make-immutable-hash
                                  (hash->list (hash-ref connect (ainst-name ins) (hash))))])))
      (amod name kind params clocks ports aliases regs tables insts2 wires rules algos
            (loc->info path (and file (loc file #f #f)))))))
