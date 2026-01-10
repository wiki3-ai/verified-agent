; Chat OpenAI - Interactive Demo with OpenAI Cloud Provider
; =========================================================
; This file demonstrates using OpenAI's API instead of a local LLM.
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

(defconst *openai-model* "gpt-5.2")

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
  "Start an interactive chat session with OpenAI gpt-5.2.
   Uses OPENAI_API_KEY environment variable for authentication."
  (declare (xargs :mode :program :stobjs state))
  (interactive-chat-loop-with-provider *initial-chat-state* *openai-config* state))

;;;============================================================================
;;; Usage Instructions
;;;============================================================================

(value-triple 
 (cw "~%OpenAI Chat loaded (model: ~s0)~%Run: (chat-openai state)~%~%" 
     *openai-model*))
