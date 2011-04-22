;; Mode for CIC^-
;; Mostly taken from haskell mode and wpdl mode

(defvar cicminus-mode-hook nil)
(defvar cicminus-mode-map
  (let ((cicminus-mode-map (make-keymap)))
    (define-key cicminus-mode-map "\C-j" 'newline-and-indent)
    cicminus-mode-map)
  "Keymap for CIC^- major mode")

(add-to-list 'auto-mode-alist '("\\.cic\\'" . cicminus-mode))
;; Syntax table.
;; Stolen from haskell mode
(defvar cicminus-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\  " " table)
    (modify-syntax-entry ?\t " " table)
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\' "\'" table)
    (modify-syntax-entry ?_  "w" table)
    (modify-syntax-entry ?\( "()" table)
    (modify-syntax-entry ?\) ")(" table)
    (modify-syntax-entry ?\[  "(]" table)
    (modify-syntax-entry ?\]  ")[" table)

    (modify-syntax-entry ?\{  "(}1nb" table)
    (modify-syntax-entry ?\}  "){4nb" table)
    (modify-syntax-entry ?-  "_ 123" table)
    (modify-syntax-entry ?\n ">" table)
    (mapc (lambda (x)
            (modify-syntax-entry x "_" table))
          ;; Some of these are actually OK by default.
          "+<@|=>:")
  table)
  "Syntax table for CIC^-")



;; Font lock
;; Stolen from cicminus-mode
(defconst cicminus-font-lock-keywords-1
  (list
   ;; Built using
   ;; (regexp-opt '("define" "assume" "data" "forall" "fun" "with" "where" "of" "case" "fix" "end" "in") t)
   '("\\<\\(assume\\|case\\|d\\(?:ata\\|efine\\)\\|end\\|f\\(?:ix\\|orall\\|un\\)\\|in\\|of\\|w\\(?:here\\|ith\\)\\)\\>" . font-lock-builtin-face)
   '("\\('\\w*'\\)" . font-lock-variable-name-face))
  "Highlighting for CIC^-")

(defconst cicminus-font-lock-keywords-2
  (append cicminus-font-lock-keywords-1
          (list
           '("\\<\\(Prop\\|Type\\)\\>" . font-lock-constant-face)))
  "Constants in CIC^-.")

(defconst cicminus-font-lock-keywords-3
  (append cicminus-font-lock-keywords-2
          (list
           '(;; (regexp-opt '(":" ":=" "|" "->" "=>" ",") t)
             "\\S_\\(->\\|:=\\|=>\\|[,:|]\\)\\S_"
           . font-lock-type-face)))
  "Constants in CIC^-.")


(defvar cicminus-font-lock-keywords cicminus-font-lock-keywords-2
  "Default highlighting expressions for CIC^- mode.")


(defun cicminus-mode ()
  (interactive)
  (kill-all-local-variables)
  (use-local-map cicminus-mode-map)
  (set-syntax-table cicminus-syntax-table)
  ;; Set up font-lock
  (set (make-local-variable 'font-lock-defaults) '(cicminus-font-lock-keywords))
  ;; Register our indentation function
  ;; (set (make-local-variable 'indent-line-function) 'cicminus-indent-line)
  (setq major-mode 'cicminus-mode)
  (setq mode-name "CIC^-")
  (run-hooks 'cicminus-mode-hook))

(provide 'cicminus-mode)
