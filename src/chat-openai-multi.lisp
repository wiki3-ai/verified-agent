; Chat OpenAI - Interactive Demo with OpenAI Cloud Provider
; =========================================================
; This file demonstrates using OpenAI's API instead of a local LLM.
;
; Prerequisites:
;   1. Get an API key from https://platform.openai.com/api-keys
;   2. Start the MCP server: mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment
;
; Usage (interactive):
;   cd src
;   acl2
;   (ld "chat-openai.lisp")
;   ;; Enter your API key when prompted, or set it below
;   (interactive-chat-loop-with-provider *initial-chat-state* *openai-config* state)
;
; Usage (non-interactive with hardcoded key):
;   1. Replace "YOUR-API-KEY-HERE" below with your actual key
;   2. Run: (ld "chat-openai.lisp")

(in-package "ACL2")

;;;============================================================================
;;; Load common definitions
;;;============================================================================

(include-book "chat-lib"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client) (:mcp-client)))

;;;============================================================================
;;; OpenAI Configuration
;;;============================================================================

;; OPTION 1: Set your API key here (not recommended for shared code)
;; (defconst *openai-api-key* "sk-...")

;; OPTION 2: Use environment variable (recommended)
;; Set OPENAI_API_KEY in your environment before starting ACL2

;; Available OpenAI models (as of 2025):
;;   - "gpt-4o"          : Most capable, best for complex reasoning
;;   - "gpt-4o-mini"     : Fast and cheap, good for most tasks
;;   - "gpt-4-turbo"     : Previous generation, 128k context
;;   - "gpt-3.5-turbo"   : Fastest, cheapest, good for simple tasks
;;   - "o1-preview"      : Reasoning model (slower, more thorough)
;;   - "o1-mini"         : Smaller reasoning model

(defconst *default-openai-model* "gpt-5.1-codex")

;;;============================================================================
;;; Helper to read API key
;;;============================================================================

;; Simple function to prompt for API key if not set
(defun get-openai-api-key-interactive (state)
  "Prompt user for OpenAI API key."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%Enter your OpenAI API key (sk-...): ")
    (mv-let (line state)
      (read-line-from-user state)
      (if (and line (> (length line) 0))
          (mv line state)
        (mv nil state)))))

;;;============================================================================
;;; Create Provider Config
;;;============================================================================

;; Default config - you can modify the model here
(defconst *openai-config*
  (make-openai-provider-config 
   "YOUR-API-KEY-HERE"  ; Replace with your key or use setup-openai below
   *default-openai-model*))

;; Alternative configs for different models
(defconst *openai-gpt4o-config*
  (make-openai-provider-config "YOUR-API-KEY-HERE" "gpt-4o"))

(defconst *openai-gpt35-config*
  (make-openai-provider-config "YOUR-API-KEY-HERE" "gpt-3.5-turbo"))

;;;============================================================================
;;; Interactive Setup (prompts for API key)
;;;============================================================================

(defun setup-openai-config (model state)
  "Interactively set up OpenAI config by prompting for API key."
  (declare (xargs :mode :program :stobjs state))
  (mv-let (api-key state)
    (get-openai-api-key-interactive state)
    (if (null api-key)
        (prog2$ (cw "~%No API key provided. Cannot create config.~%")
                (mv nil state))
      (let ((config (make-openai-provider-config api-key model)))
        (prog2$ (cw "~%Created OpenAI config for model: ~s0~%" model)
                (mv config state))))))

;;;============================================================================
;;; Quick Start Functions
;;;============================================================================

(defun chat-with-openai (api-key state)
  "Start an interactive chat session with OpenAI using the given API key.
   Example: (chat-with-openai \"sk-...\" state)"
  (declare (xargs :mode :program :stobjs state))
  (let ((config (make-openai-provider-config api-key *default-openai-model*)))
    (interactive-chat-loop-with-provider *initial-chat-state* config state)))

(defun chat-with-gpt4o (api-key state)
  "Start an interactive chat session with GPT-4o (most capable model).
   Example: (chat-with-gpt4o \"sk-...\" state)"
  (declare (xargs :mode :program :stobjs state))
  (let ((config (make-openai-provider-config api-key "gpt-4o")))
    (interactive-chat-loop-with-provider *initial-chat-state* config state)))

(defun chat-with-gpt35 (api-key state)
  "Start an interactive chat session with GPT-3.5-turbo (fastest/cheapest).
   Example: (chat-with-gpt35 \"sk-...\" state)"
  (declare (xargs :mode :program :stobjs state))
  (let ((config (make-openai-provider-config api-key "gpt-3.5-turbo")))
    (interactive-chat-loop-with-provider *initial-chat-state* config state)))

;;;============================================================================
;;; Single Query Example
;;;============================================================================

(defun ask-openai (api-key question state)
  "Send a single question to OpenAI and print the response.
   Example: (ask-openai \"sk-...\" \"What is 2+2?\" state)"
  (declare (xargs :mode :program :stobjs state))
  (let* ((config (make-openai-provider-config api-key *default-openai-model*))
         (messages (list (make-user-message question))))
    (prog2$ (cw "~%Asking OpenAI (~s0): ~s1~%" *default-openai-model* question)
      (mv-let (err response state)
        (llm-chat-completion-with-provider config messages state)
        (if err
            (prog2$ (cw "~%Error: ~s0~%" err)
                    (mv err state))
          (prog2$ (cw "~%Response: ~s0~%" response)
                  (mv response state)))))))

;;;============================================================================
;;; Usage Instructions
;;;============================================================================

(defconst *openai-usage-message*
  "
================================================================================
                        OpenAI Chat Demo Loaded
================================================================================

Quick Start (replace sk-... with your actual API key):

  ;; Interactive chat session
  (chat-with-openai \"sk-...\" state)

  ;; Use GPT-4o (most capable)
  (chat-with-gpt4o \"sk-...\" state)

  ;; Use GPT-3.5-turbo (fastest/cheapest)
  (chat-with-gpt35 \"sk-...\" state)

  ;; Single question
  (ask-openai \"sk-...\" \"What is the factorial of 5?\" state)

  ;; Manual setup with custom model
  (let ((config (make-openai-provider-config \"sk-...\" \"gpt-4o-mini\")))
    (interactive-chat-loop-with-provider *initial-chat-state* config state))

Available Models:
  - gpt-4o        : Most capable, best reasoning
  - gpt-4o-mini   : Fast, cheap, good for most tasks (default)
  - gpt-4-turbo   : Previous gen, 128k context
  - gpt-3.5-turbo : Fastest, cheapest

Type /exit or /quit to end a chat session.
================================================================================
")

;; Print usage on load
(value-triple (cw "~s0" *openai-usage-message*))
