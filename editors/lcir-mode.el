;;; lcir-mode.el --- Major mode for LispCircuit (.lcir) sources  -*- lexical-binding: t; -*-

;; Keywords: languages, hardware
;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; LCIR sources are S-expressions restricted to a subset that both the
;; Racket compiler and the Emacs Lisp reader accept.  This mode derives
;; from `lisp-data-mode', so paredit, `forward-sexp', `read' and friends
;; work unchanged; it only adds highlighting, indentation and a
;; compile command.
;;
;;   (add-to-list 'load-path "/path/to/LispCircuit/editors")
;;   (require 'lcir-mode)
;;
;; M-x lcir-check runs `racket lcir/cli.rkt check' on the current file and
;; jumps to diagnostics through `compilation-mode'.

;;; Code:

(require 'compile)

(defgroup lcir nil
  "LispCircuit hardware description language."
  :group 'languages)

(defcustom lcir-racket-program "racket"
  "Racket executable used to run the LCIR compiler."
  :type 'string)

(defcustom lcir-cli nil
  "Path to lcir/cli.rkt.  When nil, search upward from the buffer's file."
  :type '(choice (const nil) file))

(defconst lcir-definers
  '("defmodule" "defsystem" "defrule" "defalgo" "defenum" "defmacro"))

(defconst lcir-builtins
  '("gen-for" "cat-for" "reduce-tree" "symcat" "log2" "clog2" "infix" "include"
    "set!" "table-write" "table-read" "table-rdata" "drive" "log" "check" "finish"
    "mux" "match" "let" "if" "field" "idx" "pack" "vlit" "cat" "bits"
    "zext" "sext" "trunc" "as-uint" "as-sint" "valid" "ready"
    "wire" "assign" "uint" "sint" "bundle" "vec" "stream" "u" "s"))

(defconst lcir-font-lock-keywords
  `((,(concat "(" (regexp-opt lcir-definers t) "\\_>[ \t]*\\(\\(?:\\sw\\|\\s_\\)+\\)?")
     (1 font-lock-keyword-face)
     (2 font-lock-function-name-face nil t))
    (,(concat "(" (regexp-opt lcir-builtins t) "\\_>")
     (1 font-lock-builtin-face))
    ("\\_<:\\(?:\\sw\\|\\s_\\)+\\_>" . font-lock-constant-face)
    ("\\_<\\(?:t\\|nil\\)\\_>" . font-lock-constant-face)))

;; Only LCIR-specific heads get indent specs, so plain Emacs Lisp
;; indentation of `let' and friends is left alone.
(dolist (spec '((defmodule . 1) (defsystem . 1) (defrule . 1) (defalgo . 3)
                (defenum . 1) (gen-for . 1) (cat-for . 1) (reduce-tree . 2)
                (mux . 1)))
  (put (car spec) 'lisp-indent-function (cdr spec)))

(defun lcir--cli ()
  (or lcir-cli
      (let ((root (and buffer-file-name
                       (locate-dominating-file buffer-file-name "lcir/cli.rkt"))))
        (and root (expand-file-name "lcir/cli.rkt" root)))
      (user-error "Cannot find lcir/cli.rkt; set `lcir-cli'")))

(defun lcir-check ()
  "Type-check the current file with the LCIR compiler."
  (interactive)
  (save-buffer)
  (compile (format "%s %s check %s"
                   lcir-racket-program
                   (shell-quote-argument (lcir--cli))
                   (shell-quote-argument buffer-file-name))))

(with-eval-after-load 'compile
  (add-to-list 'compilation-error-regexp-alist-alist
               '(lcir "^  at: \\([^:\n]+\\):\\([0-9]+\\):\\([0-9]+\\)" 1 2 3))
  (add-to-list 'compilation-error-regexp-alist 'lcir))

(defvar lcir-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-c") #'lcir-check)
    m))

;;;###autoload
(define-derived-mode lcir-mode lisp-data-mode "LCIR"
  "Major mode for LispCircuit sources."
  (setq-local font-lock-defaults '(lcir-font-lock-keywords nil nil))
  (setq-local comment-start ";; "))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lcir\\'" . lcir-mode))

(provide 'lcir-mode)
;;; lcir-mode.el ends here
