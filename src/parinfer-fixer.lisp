; parinfer-fixer.lisp - Fix unbalanced parentheses in LLM-generated Lisp code
;
; Copyright (C) 2025
;
; License: See LICENSE file
;
; This module uses parinfer-rust to fix common parenthesis errors in
; LLM-generated ACL2/Common Lisp code. LLMs often produce syntactically
; valid-looking code with incorrect indentation-to-paren correspondence.
;
; Parinfer's "indent mode" infers parentheses from indentation, which is
; exactly what we need since LLMs usually get indentation right but parens wrong.

(in-package "ACL2")

;;;============================================================================
;;; Configuration
;;;============================================================================

;; Path to parinfer-rust executable (must be in PATH after sourcing cargo env)
;; We'll call it via shell since there's no direct FFI
(defconst *parinfer-rust-cmd* "parinfer-rust")

;; Mode for parinfer:
;;   "indent" - Infer parens from indentation (best for LLM output)
;;   "paren"  - Infer indentation from parens
;;   "smart"  - Try to be smart about what to fix
(defconst *parinfer-default-mode* "indent")

;; Language option for Common Lisp / ACL2 (enables #| |# block comments)
(defconst *parinfer-lisp-options* "--lisp-block-comments")

;;;============================================================================
;;; Shell Command Execution (Program Mode)
;;;============================================================================

;; Execute a shell command with input string and return output
;; Returns (mv error-string output-string state)
(defun run-shell-command-with-input (cmd input-str state)
  (declare (xargs :mode :program :stobjs state))
  (b* (;; Write input to a temp file
       (temp-in "/tmp/parinfer-input.lisp")
       (temp-out "/tmp/parinfer-output.lisp")
       ;; Write the input
       ((mv channel state)
        (open-output-channel temp-in :character state))
       ((when (not channel))
        (mv "Failed to open temp input file" "" state))
       (state (princ$ input-str channel state))
       (state (close-output-channel channel state))
       ;; Run the command: cmd < temp-in > temp-out
       (full-cmd (concatenate 'string cmd " < " temp-in " > " temp-out " 2>&1"))
       ((mv exit-code state) (sys-call+ "sh" (list "-c" full-cmd) state))
       ;; Read the output
       ((mv output state) (read-file-into-string temp-out state)))
    (if (and (eql exit-code 0) output)
        (mv nil output state)
      (mv (concatenate 'string "Command failed with exit code: " 
                       (coerce (explode-atom exit-code 10) 'string))
          (or output "") state))))

;;;============================================================================
;;; Parinfer Interface
;;;============================================================================

;; Fix Lisp code using parinfer-rust indent mode
;; This infers correct parentheses from the code's indentation
;; Returns (mv error-string fixed-code state)
(defun parinfer-fix-code (code state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((cmd (concatenate 'string 
                           *parinfer-rust-cmd* 
                           " -m " *parinfer-default-mode*
                           " " *parinfer-lisp-options*)))
    (run-shell-command-with-input cmd code state)))

;; Fix code with explicit mode selection
;; mode should be "indent", "paren", or "smart"
(defun parinfer-fix-code-with-mode (code mode state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((cmd (concatenate 'string 
                           *parinfer-rust-cmd* 
                           " -m " mode
                           " " *parinfer-lisp-options*)))
    (run-shell-command-with-input cmd code state)))

;;;============================================================================
;;; Code Validation
;;;============================================================================

;; Check if parentheses are balanced in a string
;; Returns t if balanced, nil otherwise
;; Note: This is a simple check that doesn't handle strings/comments
(defun parens-balanced-simple (str)
  (declare (xargs :mode :program))
  (let ((chars (coerce str 'list)))
    (parens-balanced-simple-aux chars 0 0 0)))

(defun parens-balanced-simple-aux (chars parens brackets braces)
  (declare (xargs :mode :program))
  (if (endp chars)
      (and (= parens 0) (= brackets 0) (= braces 0))
    (let ((ch (car chars)))
      (cond
        ((eql ch #\() (parens-balanced-simple-aux (cdr chars) (1+ parens) brackets braces))
        ((eql ch #\)) (if (> parens 0)
                          (parens-balanced-simple-aux (cdr chars) (1- parens) brackets braces)
                        nil)) ; Unmatched close paren
        ((eql ch #\[) (parens-balanced-simple-aux (cdr chars) parens (1+ brackets) braces))
        ((eql ch #\]) (if (> brackets 0)
                          (parens-balanced-simple-aux (cdr chars) parens (1- brackets) braces)
                        nil))
        ((eql ch #\{) (parens-balanced-simple-aux (cdr chars) parens brackets (1+ braces)))
        ((eql ch #\}) (if (> braces 0)
                          (parens-balanced-simple-aux (cdr chars) parens brackets (1- braces))
                        nil))
        (t (parens-balanced-simple-aux (cdr chars) parens brackets braces))))))

;;;============================================================================
;;; High-Level API for Agent Integration
;;;============================================================================

;; Check and optionally fix LLM-generated code
;; Returns (mv was-fixed error fixed-code state)
;; was-fixed is t if code was modified, nil if already correct
(defun check-and-fix-lisp-code (code state)
  (declare (xargs :mode :program :stobjs state))
  (if (parens-balanced-simple code)
      ;; Code looks balanced, but let parinfer verify structure
      (b* (((mv err fixed state) (parinfer-fix-code code state)))
        (if err
            (mv nil err code state)
          (mv (not (equal code fixed)) nil fixed state)))
    ;; Code is definitely unbalanced, fix it
    (b* (((mv err fixed state) (parinfer-fix-code code state)))
      (if err
          (mv nil err code state)
        (mv t nil fixed state)))))

;; Fix code and report what changed
;; Returns (mv report fixed-code state)
(defun fix-lisp-code-with-report (code state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((mv was-fixed err fixed state) (check-and-fix-lisp-code code state)))
    (cond
      (err (mv (concatenate 'string "[Parinfer Error] " err) code state))
      (was-fixed (mv "[Parinfer] Fixed unbalanced parentheses" fixed state))
      (t (mv nil code state)))))

;;;============================================================================
;;; Test Utilities
;;;============================================================================

;; Test parinfer on a code string (for interactive testing)
(defmacro test-parinfer (code)
  `(make-event
    (mv-let (err result state)
      (parinfer-fix-code ,code state)
      (if err
          (prog2$ (cw "Error: ~s0~%" err)
                  (mv nil '(value-triple :error) state))
        (prog2$ (cw "Result:~%~s0~%" result)
                (mv nil '(value-triple :ok) state))))))

;; Example test cases showing common LLM errors
(defconst *test-cases*
  '(;; Missing closing parens
    "(defun foo (x)\n  (+ x 1"
    ;; Extra closing paren
    "(defun bar (x)\n  (+ x 1)))"
    ;; Correct code (should be unchanged)
    "(defun baz (x)\n  (+ x 1))"
    ;; Nested with wrong closing
    "(let ((a 1)\n      (b 2))\n  (+ a b"
    ;; Multiple forms
    "(defun f1 (x) x)\n(defun f2 (y) y"
    ))
