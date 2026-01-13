(require 'org)
(require 'org-re-reveal)
(require 'htmlize)

(defmacro require-if-present (feature)
  "Call `require' on FEATURE and write a log message indicating
whether the feature could be loaded or not."
  `(if (ignore-errors (require ',feature))
       (message (concat "Loaded feature "
                        (symbol-name ',feature)))
     (message (concat "Feature "
                      (symbol-name ',feature)
                      " is not installed"))))

;; You'd add lines like these if you require syntax highlighting from
;; packages that you've added to the Emacs defined in flake.nix.  This
;; then loads the faces that are needed to define corresponding CSS
;; classes.
(require-if-present haskell)

(org-babel-do-load-languages
 'org-babel-load-languages '((plantuml . t)
                             (gnuplot . t)))
(setq org-confirm-babel-evaluate nil)
(setq org-plantuml-exec-mode 'plantuml)

;; Syntax highlighting via CSS
(setq org-html-htmlize-output-type 'css)

(defun org-re-reveal-export-file (filename &optional reveal-root reveal-mathjax-url)
  "Export FILENAME to HTML.  Optionally change or set the path to a
reveal.js checkout and a MathJax checkout."
  (interactive "f")
  (let* ((buffer (find-file-noselect filename))
         (org-re-reveal-root (or reveal-root org-re-reveal-root))
         (org-re-reveal-mathjax-url reveal-mathjax-url))
    (message (concat "Exporting " filename " to HTML"))
    (with-current-buffer buffer
      (org-re-reveal-export-to-html))))
