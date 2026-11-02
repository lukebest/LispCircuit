#lang racket
;; Readable SystemVerilog. Names come from the source; temporaries are
;; only the per-register `_we` / `_next` wires the scheduler already named.

(require "ast.rkt" "types.rkt" "nhir.rkt")
(provide sv-name mod-sv-name emit-sv-file emit-module emit-types
         sv-expr sv-const sv-fmt sv-string decl-ty
         collect-enums collect-bundles)

(define (sv-name s)
  (regexp-replace* #rx"-" (if (symbol? s) (symbol->string s) (format "~a" s)) "_"))

(define (mod-sv-name h)
  (define base (sv-name (hmod-name h)))
  (if (null? (hmod-params h))
      base
      (apply string-append base
             (for/list ([p (hmod-params h)])
               (format "_~a~a" (sv-name (car p)) (cdr p))))))

(define (sv-string s)
  (string-append
   "\""
   (apply string-append
          (for/list ([c (in-string s)])
            (case c
              [(#\\) "\\\\"]
              [(#\") "\\\""]
              [(#\newline) "\\n"]
              [else (string c)])))
   "\""))

(define (type-tag t)
  (match t
    [(ty-uint w) (format "u~a" w)]
    [(ty-sint w) (format "s~a" w)]
    [(ty-enum n _) (format "e~a" (sv-name n))]
    [(ty-bundle _) (bundle-name t)]
    [(ty-vec n e) (format "v~a_~a" n (type-tag e))]
    [(ty-stream e) (format "st_~a" (type-tag e))]
    [_ "t"]))

(define (bundle-name t)
  (format "bundle_~a"
          (string-join
           (for/list ([f (ty-bundle-fields t)])
             (format "~a_~a" (sv-name (car f)) (type-tag (cdr f))))
           "_")))

(define (split-vec t)
  (match t
    [(ty-vec n e)
     (define-values (b dims) (split-vec e))
     (values b (cons n dims))]
    [else (values t '())]))

(define (sv-base t)
  (match t
    [(ty-uint 1) "logic"]
    [(ty-uint w) (format "logic [~a:0]" (sub1 w))]
    [(ty-sint 1) "logic signed"]
    [(ty-sint w) (format "logic signed [~a:0]" (sub1 w))]
    [(ty-enum n _) (sv-name n)]
    [(ty-bundle _) (bundle-name t)]
    [_ "logic"]))

(define (decl-ty t name)
  (define-values (b dims) (split-vec t))
  (format "~a ~a~a"
          (sv-base b)
          (sv-name name)
          (apply string-append (map (lambda (n) (format " [0:~a]" (sub1 n))) dims))))

(define (sv-const v t)
  (match t
    [(ty-uint w) (format "~a'd~a" w v)]
    [(ty-sint w)
     (if (negative? v) (format "-~a'sd~a" w (- v)) (format "~a'sd~a" w v))]
    [(ty-enum _ vs) (sv-name (list-ref vs v))]
    [(ty-bundle fs)
     (format "'{~a}"
             (string-join
              (for/list ([f fs])
                (format "~a:~a" (sv-name (car f)) (sv-const (hash-ref v (car f)) (cdr f))))
              ", "))]
    [(ty-vec n e)
     (format "'{~a}"
             (string-join (for/list ([i (in-range n)]) (sv-const (vector-ref v i) e)) ", "))]
    [_ (format "~a" v)]))

(define (sv-fit e w)
  (define t (expr-ty e))
  (define aw (ty-width t))
  (cond
    [(>= aw w) (sv-expr e)]
    [(or (ty-sint? t) (ty-enum? t))
     (format "{{(~a){~a[~a]}}, ~a}" (- w aw) (sv-expr e) (sub1 aw) (sv-expr e))]
    [else
     (format "{{(~a){1'b0}}, ~a}" (- w aw) (sv-expr e))]))

(define (sv-binop op a b t)
  (define (bin sym) (format "(~a ~a ~a)" (sv-expr a) sym (sv-expr b)))
  (case op
    [(+ - * & ^) (bin (symbol->string op))]
    [(\|) (bin "|")]
    [(+) (bin "+")]
    [(== != < <= > >=) (bin (symbol->string op))]
    [(and) (bin "&&")]
    [(or) (bin "||")]
    [(<<) (bin "<<")]
    [(>>) (bin (if (ty-sint? (expr-ty a)) ">>>" ">>"))]
    [(+w) (format "(~a + ~a)" (sv-fit a (ty-width t)) (sv-fit b (ty-width t)))]
    [(-w) (format "(~a - ~a)" (sv-fit a (ty-width t)) (sv-fit b (ty-width t)))]
    [(*w) (format "(~a * ~a)" (sv-fit a (ty-width t)) (sv-fit b (ty-width t)))]
    [else (bin (symbol->string op))]))

(define (sv-expr e)
  (match e
    [(e-lit v t _) (sv-const v t)]
    [(e-ref n _ _) (sv-name n)]
    [(e-child i p _ _) (sv-name (string->symbol (format "~a_~a" i p)))]
    [(e-binop op a b t _) (sv-binop op a b t)]
    [(e-unop 'not a _ _) (format "(!(~a))" (sv-expr a))]
    [(e-unop '~ a _ _) (format "(~~~a)" (sv-expr a))]
    [(e-unop '- a _ _) (format "(-(~a))" (sv-expr a))]
    [(e-mux c t f _ _) (format "(~a ? ~a : ~a)" (sv-expr c) (sv-expr t) (sv-expr f))]
    [(e-field b f _ _) (format "~a.~a" (sv-expr b) (sv-name f))]
    [(e-idx b i _ _) (format "~a[~a]" (sv-expr b) (sv-expr i))]
    [(e-cast 'zext a (ty-uint w) _)
     (define aw (ty-width (expr-ty a)))
     (if (<= w aw) (sv-expr a) (format "{{(~a){1'b0}}, ~a}" (- w aw) (sv-expr a)))]
    [(e-cast 'sext a (ty-sint w) _)
     (define aw (ty-width (expr-ty a)))
     (if (<= w aw) (sv-expr a)
         (format "{{(~a){~a[~a]}}, ~a}" (- w aw) (sv-expr a) (sub1 aw) (sv-expr a)))]
    [(e-cast 'trunc a t _)
     (define w (ty-width t))
     (if (= w 1) (format "~a[0]" (sv-expr a)) (format "~a[~a:0]" (sv-expr a) (sub1 w)))]
    [(e-cast 'as-uint a _ _) (format "$unsigned(~a)" (sv-expr a))]
    [(e-cast 'as-sint a _ _) (format "$signed(~a)" (sv-expr a))]
    [(e-slice a hi lo _ _)
     (if (= hi lo) (format "~a[~a]" (sv-expr a) lo) (format "~a[~a:~a]" (sv-expr a) hi lo))]
    [(e-cat ps _ _) (format "{~a}" (string-join (map sv-expr ps) ", "))]
    [(e-pack fs _ _)
     (format "'{~a}" (string-join (map (lambda (f) (format "~a:~a" (sv-name (car f)) (sv-expr (cdr f)))) fs) ", "))]
    [(e-vlit ps _ _) (format "'{~a}" (string-join (map sv-expr ps) ", "))]
    [(e-tread n a _ _) (format "~a[~a]" (sv-name n) (sv-expr a))]
    [(e-rdata n _ _) (format "~a_rdata" (sv-name n))]
    [_ (error 'sv-expr "cannot print ~a" e)]))

(define (sv-fmt e)
  (match (expr-ty e)
    [(or (ty-uint _) (ty-sint _)) (values "%0d" (list (sv-expr e)))]
    [(ty-enum name _)
     (values "%s" (list (format "lcir_name_~a(~a)" (sv-name name) (sv-expr e))))]
    [(ty-bundle fs)
     (define bits
       (for/list ([f fs])
         (define-values (fmt args)
           (sv-fmt (e-field e (car f) (cdr f) (expr-info e))))
         (cons (format "~a=~a" (car f) fmt) args)))
     (values (format "{~a}" (string-join (map car bits) ","))
             (append-map cdr bits))]
    [(ty-vec n elem)
     (define bits
       (for/list ([i (in-range n)])
         (define-values (fmt args)
           (sv-fmt (e-idx e (e-lit i (ty-uint (max 1 (clog2 n))) (expr-info e))
                          elem (expr-info e))))
         (cons fmt args)))
     (values (format "[~a]" (string-join (map car bits) ","))
             (append-map cdr bits))]
    [_ (values "%0d" (list (sv-expr e)))]))

(define (walk-type t enums bundles)
  (match t
    [(ty-enum n vs)
     (hash-set! enums n vs)
     (values enums bundles)]
    [(ty-bundle fs)
     (hash-set! bundles (bundle-name t) t)
     (for ([f fs]) (walk-type (cdr f) enums bundles))
     (values enums bundles)]
    [(ty-vec _ e) (walk-type e enums bundles)]
    [(ty-stream e) (walk-type e enums bundles)]
    [_ (values enums bundles)]))

(define (collect-from-hmod h enums bundles)
  (for ([p (hmod-ports h)]) (walk-type (hport-ty p) enums bundles))
  (for ([r (hmod-regs h)]) (walk-type (hreg-ty r) enums bundles))
  (for ([w (hmod-wires h)]) (walk-type (hwire-ty w) enums bundles))
  (for ([t (hmod-tables h)]) (walk-type (htable-elem-ty t) enums bundles))
  (for ([i (hmod-insts h)]) (collect-from-hmod (hinst-mod i) enums bundles)))

(define (collect-enums mods)
  (define enums (make-hash))
  (define bundles (make-hash))
  (for ([h mods]) (collect-from-hmod h enums bundles))
  enums)

(define (collect-bundles mods)
  (define enums (make-hash))
  (define bundles (make-hash))
  (for ([h mods]) (collect-from-hmod h enums bundles))
  bundles)

(define (emit-types mods)
  (define enums (collect-enums mods))
  (define bundles (collect-bundles mods))
  (define lines
    (append
     (list "package lcir_types;")
     (for/list ([(name vs) (in-hash enums)])
       (define w (max 1 (integer-length (max 1 (sub1 (length vs))))))
       (format "  typedef enum logic [~a:0] { ~a } ~a;"
               (sub1 w)
               (string-join
                (for/list ([v vs] [i (in-naturals)])
                  (format "~a = ~a" (sv-name v) i))
                ", ")
               (sv-name name)))
     (for/list ([(n t) (in-hash bundles)])
       (format "  typedef struct packed { ~a } ~a;"
               (string-join
                (for/list ([f (ty-bundle-fields t)])
                  (format "~a ~a;" (sv-base (cdr f)) (sv-name (car f))))
                " ")
               n))
     (for/list ([(name vs) (in-hash enums)])
       (format "  function automatic string lcir_name_~a(input ~a s);\n    case (s)\n~a\n      default: return \"?\";\n    endcase\n  endfunction"
               (sv-name name)
               (sv-name name)
               (string-join
                (for/list ([v vs])
                  (format "      ~a: return \"~a\";" (sv-name v) v))
                "\n")))
     (list "endpackage")))
  (string-append "`ifndef LCIR_TYPES\n`define LCIR_TYPES\n"
                 (string-join lines "\n")
                 "\n`endif\n"))

(define (port-list h)
  (append
   (for/list ([c (hmod-clocks h)])
     (format "  input logic ~a" (sv-name c)))
   (list "  input logic rst")
   (for/list ([p (hmod-ports h)])
     (format "  ~a ~a" (if (eq? (hport-dir p) 'in) "input" "output")
             (let ([d (decl-ty (hport-ty p) (hport-name p))])
               ;; decl-ty includes the name; direction is separate, so drop the duplicate "logic" prefix handling
               d)))))

(define (emit-module h #:wrapped [wrapped #t])
  (define out-names (list->set (map hport-name (filter (lambda (p) (eq? (hport-dir p) 'out)) (hmod-ports h)))))
  (define lines
    (append
     (if wrapped
         (list (format "module ~a (" (mod-sv-name h))
               (string-join (port-list h) ",\n")
               ");")
         '())
     (list "  import lcir_types::*;")
     (for/list ([r (hmod-regs h)])
       (format "  ~a;" (decl-ty (hreg-ty r) (hreg-name r))))
     (for/list ([r (hmod-regs h)])
       (format "  ~a;\n  ~a;"
               (decl-ty (ty-uint 1) (string->symbol (format "~a_we" (hreg-name r))))
               (decl-ty (hreg-ty r) (string->symbol (format "~a_next" (hreg-name r))))))
     (for/list ([w (hmod-wires h)] #:unless (set-member? out-names (hwire-name w)))
       (format "  ~a;" (decl-ty (hwire-ty w) (hwire-name w))))
     (for/list ([t (hmod-tables h)])
       (string-join
        (append
         (list (format "  ~a [0:~a];" (decl-ty (htable-elem-ty t) (htable-name t)) (sub1 (htable-depth t)))
               (format "  ~a;" (decl-ty (ty-uint 1) (string->symbol (format "~a_we" (htable-name t)))))
               (format "  ~a;" (decl-ty (ty-uint (max 1 (integer-length (max 1 (sub1 (htable-depth t))))))
                                        (string->symbol (format "~a_waddr" (htable-name t)))))
               (format "  ~a;" (decl-ty (htable-elem-ty t) (string->symbol (format "~a_wdata" (htable-name t))))))
         (if (= (htable-latency t) 1)
             (list (format "  ~a;" (decl-ty (ty-uint 1) (string->symbol (format "~a_re" (htable-name t)))))
                   (format "  ~a;" (decl-ty (ty-uint (max 1 (integer-length (max 1 (sub1 (htable-depth t))))))
                                            (string->symbol (format "~a_raddr" (htable-name t)))))
                   (format "  ~a;" (decl-ty (htable-elem-ty t) (string->symbol (format "~a_rdata" (htable-name t))))))
             '()))
        "\n"))
     (for/list ([ins (hmod-insts h)])
       (apply string-append
              (for/list ([p (hmod-ports (hinst-mod ins))])
                (format "  ~a;\n" (decl-ty (hport-ty p)
                                           (string->symbol (format "~a_~a" (hinst-name ins) (hport-name p))))))))
     (for/list ([r (hmod-regs h)])
       (format "  assign ~a_we = ~a;\n  assign ~a_next = ~a;"
               (sv-name (hreg-name r)) (sv-expr (hreg-we r))
               (sv-name (hreg-name r)) (sv-expr (hreg-next r))))
     (for/list ([w (hmod-wires h)])
       (format "  assign ~a = ~a;" (sv-name (hwire-name w)) (sv-expr (hwire-expr w))))
     (for/list ([t (hmod-tables h)])
       (string-join
        (append
         (list (format "  assign ~a_we = ~a;" (sv-name (htable-name t)) (sv-expr (htable-wen t)))
               (format "  assign ~a_waddr = ~a;" (sv-name (htable-name t)) (sv-expr (htable-waddr t)))
               (format "  assign ~a_wdata = ~a;" (sv-name (htable-name t)) (sv-expr (htable-wdata t))))
         (if (= (htable-latency t) 1)
             (list (format "  assign ~a_re = ~a;" (sv-name (htable-name t)) (sv-expr (htable-ren t)))
                   (format "  assign ~a_raddr = ~a;" (sv-name (htable-name t)) (sv-expr (htable-raddr t))))
             '()))
        "\n"))
     (for/list ([ins (hmod-insts h)])
       (apply string-append
              (for/list ([p (hmod-ports (hinst-mod ins))] #:when (eq? (hport-dir p) 'in))
                (define wire (sv-name (string->symbol (format "~a_~a" (hinst-name ins) (hport-name p)))))
                (define ex (hash-ref (hinst-connects ins) (hport-name p) #f))
                (if ex
                    (format "  assign ~a = ~a;\n" wire (sv-expr ex))
                    ""))))
     (for/list ([ins (hmod-insts h)])
       (define child (hinst-mod ins))
       (define conns
         (append
          (for/list ([c (hmod-clocks child)])
            (format "    .~a(~a)" (sv-name c) (sv-name c)))
          (list "    .rst(rst)")
          (for/list ([p (hmod-ports child)])
            (format "    .~a(~a)"
                    (sv-name (hport-name p))
                    (sv-name (string->symbol (format "~a_~a" (hinst-name ins) (hport-name p))))))))
       (format "  ~a ~a (\n~a\n  );" (mod-sv-name child) (sv-name (hinst-name ins))
               (string-join conns ",\n")))
     (let ([by-clk (make-hash)])
       (for ([r (hmod-regs h)])
         (hash-update! by-clk (hreg-clock r) (lambda (v) (append v (list (cons 'reg r)))) '()))
       (for ([t (hmod-tables h)])
         (hash-update! by-clk (htable-clock t) (lambda (v) (append v (list (cons 'tbl t)))) '()))
       (for/list ([(clk items) (in-hash by-clk)])
         (define resets (filter (lambda (it) (and (eq? (car it) 'reg) (not (hreg-reset-less? (cdr it))))) items))
         (define others (filter (lambda (it) (or (eq? (car it) 'tbl)
                                                (and (eq? (car it) 'reg) (hreg-reset-less? (cdr it)))))
                                items))
         (format "  always_ff @(posedge ~a) begin\n~a~a  end"
                 (sv-name clk)
                 (if (null? resets)
                     ""
                     (format "    if (rst) begin\n~a    end else begin\n~a    end\n"
                             (apply string-append
                                    (for/list ([it resets])
                                      (format "      ~a <= ~a;\n"
                                              (sv-name (hreg-name (cdr it)))
                                              (sv-const (hreg-init (cdr it)) (hreg-ty (cdr it))))))
                             (apply string-append
                                    (for/list ([it resets])
                                      (format "      if (~a_we) ~a <= ~a_next;\n"
                                              (sv-name (hreg-name (cdr it)))
                                              (sv-name (hreg-name (cdr it)))
                                              (sv-name (hreg-name (cdr it))))))))
                 (apply string-append
                        (for/list ([it others])
                          (if (eq? (car it) 'reg)
                              (format "    if (~a_we) ~a <= ~a_next;\n"
                                      (sv-name (hreg-name (cdr it)))
                                      (sv-name (hreg-name (cdr it)))
                                      (sv-name (hreg-name (cdr it))))
                              (let ([t (cdr it)])
                                (string-append
                                 (if (= (htable-latency t) 1)
                                     (format "    if (rst) ~a_rdata <= ~a;\n    else if (~a_re) ~a_rdata <= ~a[~a_raddr];\n"
                                             (sv-name (htable-name t))
                                             (sv-const (zero-value-sv (htable-elem-ty t)) (htable-elem-ty t))
                                             (sv-name (htable-name t))
                                             (sv-name (htable-name t))
                                             (sv-name (htable-name t))
                                             (sv-name (htable-name t)))
                                     "")
                                 (format "    if (~a_we) ~a[~a_waddr] <= ~a_wdata;\n"
                                         (sv-name (htable-name t))
                                         (sv-name (htable-name t))
                                         (sv-name (htable-name t))
                                         (sv-name (htable-name t)))))))))))
     (for/list ([t (hmod-tables h)])
       (format "  initial begin\n    for (int ~a_i = 0; ~a_i < ~a; ~a_i = ~a_i + 1) ~a[~a_i] = ~a;\n  end"
               (sv-name (htable-name t)) (sv-name (htable-name t)) (htable-depth t)
               (sv-name (htable-name t)) (sv-name (htable-name t))
               (sv-name (htable-name t)) (sv-name (htable-name t))
               (sv-const (zero-value-sv (htable-elem-ty t)) (htable-elem-ty t))))
     (for/list ([r (hmod-regs h)])
       (format "  initial ~a = ~a;" (sv-name (hreg-name r)) (sv-const (hreg-init r) (hreg-ty r))))
     (if wrapped (list "endmodule") '())))
  (string-join (filter non-empty-string? (flatten-strs lines)) "\n"))

(define (flatten-strs xs)
  (append-map (lambda (x) (if (list? x) (flatten-strs x) (list x))) xs))

(define (zero-value-sv t)
  (match t
    [(or (ty-uint _) (ty-sint _) (ty-enum _ _)) 0]
    [(ty-bundle fs)
     (make-immutable-hash (for/list ([f fs]) (cons (car f) (zero-value-sv (cdr f)))))]
    [(ty-vec n e) (build-vector n (lambda (_) (zero-value-sv e)))]
    [_ 0]))

(define (emit-sv-file h)
  (string-append
   "// Generated by LCIR. Names follow the source.\n"
   "/* verilator lint_off UNUSED */\n"
   "/* verilator lint_off UNUSEDSIGNAL */\n"
   "/* verilator lint_off MULTIDRIVEN */\n"
   "`include \"lcir_types.sv\"\n"
   (emit-module h)
   "\n"))
