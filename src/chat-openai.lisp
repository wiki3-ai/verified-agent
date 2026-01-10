; Chat OpenAI - Interactive Demo with OpenAI Cloud Provider
; =========================================================
; This file demonstrates using OpenAI's Codex API instead of a local LLM.
;
; Prerequisites:
;   1. Set OPENAI_API_KEY environment variable
;   2. Start the MCP server: mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment
;
; Usage:
;   cd src
;   acl2
;   (ld "chat-openai.lisp")
;   (chat-openai state)

(in-package "ACL2")

;;;============================================================================
;;; Load common definitions
;;;============================================================================

(include-book "chat-lib"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client) (:mcp-client)))

;;;============================================================================
;;; OpenAI Configuration (uses OPENAI_API_KEY env var)
;;;============================================================================

;; Using OpenAI Codex model (uses completions API, not chat API)
(defconst *openai-model* "gpt-5.1-codex")

;; Max tokens for completions API
(defconst *codex-max-tokens* 2048)

(make-event
 (mv-let (erp api-key state)
   (getenv$ "OPENAI_API_KEY" state)
   (declare (ignore erp))
   (mv nil
       `(defconst *openai-config*
          (make-openai-provider-config ,(or api-key "") ,*openai-model*))
       state)))

;;;============================================================================
;;; Main Entry Point
;;;============================================================================

(defun chat-openai (state)
  "Start an interactive chat session with OpenAI Codex.
   Uses OPENAI_API_KEY environment variable for authentication.
   Uses the completions API (/v1/completions) since Codex is not a chat model."
  (declare (xargs :mode :program :stobjs state))
  (interactive-chat-loop-with-completions *initial-chat-state* *openai-config* 
                                          *codex-max-tokens* state))

;;;============================================================================
;;; Usage Instructions
;;;============================================================================

(value-triple 
 (cw "~%OpenAI Codex Chat loaded (model: ~s0)~%Run: (chat-openai state)~%~%" 
     *openai-model*))
