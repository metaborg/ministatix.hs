;;; ministatix.el

(defvar ministatix-mode-syntax-table nil "Syntax table for statix-mode.")

(setq ministatix-mode-syntax-table
      (let ( (synTable (make-syntax-table)))
        (modify-syntax-entry ?\/ ". 12b" synTable)
        (modify-syntax-entry ?\n "> b" synTable)
        synTable))

;; create the list for font-lock.
;; each category of keyword is given a particular face
(setq ministatix-font-lock-keywords
      (let* (
             ;; define several category of keywords
             (x-keywords '("import" "match" "true" "false" "in" "as" "query" "new"))
             (x-builtins '("edge" "end" "only" "every"))

             ;; generate regex string for each category of keywords
             (x-keywords-regexp (regexp-opt x-keywords 'words))
             (x-builtins-regexp (regexp-opt x-builtins 'words))
             )

        `(
          (,x-builtins-regexp . font-lock-constant-face)
          (,x-keywords-regexp . font-lock-keyword-face)
	  (,"=\\|->\\|\\-\\[\\|\\]->\\|:-\\||" . font-lock-keyword-face)
	  (,"\\(\\w+\\)(" (1 font-lock-function-name-face))
          )))

(define-derived-mode ministatix-mode prog-mode "ministatix mode"
  "Major mode for editing Ministatix constraint language"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((ministatix-font-lock-keywords))))


(add-to-list 'auto-mode-alist '("\\.stx\\'" . ministatix-mode))

;; add the mode to the `features' list
(provide 'ministatix-mode)
