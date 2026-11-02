;;; emacs-read.el --- check that LCIR sources are readable by the Emacs reader  -*- lexical-binding: t; -*-
(require (quote bytecomp))
;; Usage: emacs --batch -l tests/emacs-read.el -f lcir-test-read FILE...
(defun lcir-test-read ()
  (let ((bad 0))
    (dolist (f command-line-args-left)
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (condition-case err
            (let ((n 0))
              (while (progn (forward-comment (buffer-size)) (not (eobp)))
                (read (current-buffer))
                (setq n (1+ n)))
              (message "%s: %d forms" f n))
          (error (setq bad (1+ bad))
                 (message "%s:%d: %S" f (line-number-at-pos) err)))))
    (setq command-line-args-left nil)
    (kill-emacs (if (> bad 0) 1 0))))

(defun lcir-test-mode ()
  "Byte-compile and load editors/lcir-mode.el, then fontify and indent FILE."
  (let ((byte-compile-error-on-warn t)
        (el (expand-file-name "editors/lcir-mode.el")))
    (unless (byte-compile-file el) (kill-emacs 1))
    (load (concat el "c") nil t)
    (dolist (f command-line-args-left)
      (with-temp-buffer
        (insert-file-contents f)
        (lcir-mode)
        (font-lock-ensure)
        (indent-region (point-min) (point-max))
        (message "%s: lcir-mode ok" f)))
    (setq command-line-args-left nil)
    (kill-emacs 0)))
