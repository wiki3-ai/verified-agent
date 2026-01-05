; Chat - Simple Interactive Chat Interface
; =========================================
; Load this file, then use (chat "your message") to interact.
;
; Usage:
;   cd src
;   acl2
;   (ld "chat.lisp")
;   (chat "Hello, can you help me?")
;   (chat "What is 2 + 2?")
;
; The conversation persists across calls. Use (chat-reset) to start fresh.

(in-package "ACL2")

;;;============================================================================
;;; Load common definitions
;;;============================================================================

(include-book "chat-lib"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client) (:mcp-client)))

;; Enable redefinition so *chat-agent* can be updated between turns
(set-ld-redefinition-action '(:doit . :overwrite) state)

;;;============================================================================
;;; Model Selection
;;;============================================================================

(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable err))
   (let ((selected (select-completions-model models *model-prefs*)))
     (prog2$
      (if selected
          (cw "~%Model: ~s0 (~x1 tokens)~%"
              (model-info->id selected)
              (model-info->loaded-context-length selected))
        (cw "~%WARNING: No model found. Ensure LM Studio is running.~%"))
      (mv nil 
          `(defconst *chat-model* 
             ,(if selected (model-info->id selected) "no-model-found"))
          state)))))

;;;============================================================================
;;; Session State - Managed via globals
;;;============================================================================

;; Initialize fresh agent state
(defconst *initial-chat-state*
  (init-agent-conversation *default-system-prompt* *default-agent-config*))

;; Global state holders (set at load time, modified by chat functions)
;; Using make-event to create mutable state holders

(make-event
 (mv-let (mcp-err mcp-conn state)
   (mcp-connect *mcp-default-endpoint* state)
   (prog2$
    (if mcp-err
        (cw "~%MCP connection failed: ~s0~%Code execution disabled.~%" mcp-err)
      (prog2$
       (cw "~%MCP connected.~%")
       (if (mcp-connection-has-acl2-session-p mcp-conn)
           (cw "ACL2 session: ~s0~%" (mcp-connection->acl2-session-id mcp-conn))
         (cw "No persistent ACL2 session.~%"))))
    (mv nil
        `(defconst *chat-mcp* ',mcp-conn)
        state))))

;; Agent state starts fresh - we use a defconst that gets redefined
(defconst *chat-agent* *initial-chat-state*)

;;;============================================================================
;;; Simple Chat Interface
;;;============================================================================

;; The main chat function - returns new state but also redefines *chat-agent*
(defun chat-fn (msg state)
  "Send a message and get a response. Updates *chat-agent* state."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ~s0~%" msg)
    (mv-let (new-agent state)
      (chat-turn msg *chat-agent* *chat-model* *chat-mcp* state)
      (mv nil
          `(defconst *chat-agent* ',new-agent)
          state))))

;; User-facing macro for simple invocation
(defmacro chat (msg)
  "Send a message to the chat agent. Example: (chat \"Hello!\")"
  `(make-event (chat-fn ,msg state)))

;; Reset conversation to initial state
(defmacro chat-reset ()
  "Reset the conversation to initial state."
  '(progn
     (defconst *chat-agent* *initial-chat-state*)
     (value-triple :chat-reset)))

;; Show current conversation
(defmacro chat-history ()
  "Display the current conversation history."
  '(value-triple (show-conversation *chat-agent*)))

;; Show context usage
(defmacro chat-usage ()
  "Display context token usage."
  '(value-triple (show-context-usage *chat-agent*)))

;;;============================================================================
;;; Startup Message
;;;============================================================================

(defconst *chat-ready*
  (prog2$ (cw "~%========================================~%")
    (prog2$ (cw "Chat Ready!~%")
      (prog2$ (cw "========================================~%")
        (prog2$ (cw "~%Commands:~%")
          (prog2$ (cw "  (chat \"your message\")  - Send a message~%")
            (prog2$ (cw "  (chat-reset)           - Start fresh~%")
              (prog2$ (cw "  (chat-history)         - Show conversation~%")
                (prog2$ (cw "  (chat-usage)           - Show token usage~%")
                  (cw "~%"))))))))))
