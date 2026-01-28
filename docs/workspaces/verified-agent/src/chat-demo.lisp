; Chat Demo - Fixed Query Demonstration
; =====================================
; This file runs a fixed set of queries to demonstrate the ReAct agent.
; For interactive use, see chat.lisp instead.
;
; Usage (interactive):
;   cd src
;   acl2
;   (ld "chat-demo.lisp")
;
; Usage (certification):
;   cert.pl chat-demo --acl2-cmd 'env SKIP_INTERACTIVE=1 acl2'
;   or just: cert.pl chat-demo  (uses cert_env below)

; cert_param: (cert_env "SKIP_INTERACTIVE=1")

(in-package "ACL2")

;;;============================================================================
;;; Load common definitions
;;;============================================================================

(include-book "chat-lib"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client) (:mcp-client)))

;;;============================================================================
;;; Model Selection (skipped during certification)
;;;============================================================================

#-skip-interactive
(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (prog2$ 
    (if err
        (cw "~%Error getting models: ~s0~%" err)
      (progn$
       (cw "~%Available models: ~x0~%" (len models))
       (cw "Loaded completions models: ~x0~%" 
           (len (filter-loaded-completions-models models)))))
    (mv nil '(value-triple :models-listed) state))))

#-skip-interactive
(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable err))
   (let ((selected (select-completions-model models *model-prefs*)))
     (prog2$
      (if selected
          (cw "~%Selected model: ~s0 (context: ~x1 tokens)~%"
              (model-info->id selected)
              (model-info->loaded-context-length selected))
        (cw "~%WARNING: No suitable model found! Make sure LM Studio is running.~%"))
      (mv nil 
          `(defconst *model-id* 
             ,(if selected (model-info->id selected) "no-model-found"))
          state)))))

;;;============================================================================
;;; Initialize Agent State
;;;============================================================================

(defconst *demo-agent-v0*
  (init-agent-conversation *default-system-prompt* *default-agent-config*))

#-skip-interactive
(defconst *check-init*
  (prog2$ (cw "~%Agent initialized. Messages: ~x0~%" 
              (len (get-messages *demo-agent-v0*)))
          t))

;;;============================================================================
;;; Demo Query 1: Introduction
;;;============================================================================

#-skip-interactive
(defconst *demo-agent-v1*
  (add-user-msg "Hello! Can you explain what a formally verified agent is?" 
                *demo-agent-v0*))

#-skip-interactive
(defconst *show-v1*
  (show-conversation *demo-agent-v1*))

#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *demo-agent-v1*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *demo-agent-v2* *demo-agent-v1*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *demo-agent-v2* 
                        (add-assistant-msg ,response *demo-agent-v1*)) 
                 state)))))

#-skip-interactive
(defconst *show-v2*
  (show-conversation *demo-agent-v2*))

;;;============================================================================
;;; Demo Query 2: Proven Properties
;;;============================================================================

#-skip-interactive
(defconst *demo-agent-v3*
  (add-user-msg "What properties have been proven about this agent?" 
                *demo-agent-v2*))

#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *demo-agent-v3*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *demo-agent-v4* *demo-agent-v3*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *demo-agent-v4* 
                        (add-assistant-msg ,response *demo-agent-v3*)) 
                 state)))))

#-skip-interactive
(defconst *show-v4*
  (show-conversation *demo-agent-v4*))

;;;============================================================================
;;; Demo Query 3: Context Management
;;;============================================================================

#-skip-interactive
(defconst *demo-agent-v5*
  (add-user-msg "That's impressive! How does the context management work?" 
                *demo-agent-v4*))

#-skip-interactive
(make-event
 (mv-let (err response state)
   (llm-chat-completion *model-id* (get-messages *demo-agent-v5*) state)
   (if err
       (prog2$ (cw "~%LLM Error: ~s0~%" err)
               (mv nil `(defconst *demo-agent-v6* *demo-agent-v5*) state))
     (prog2$ (cw "~%Assistant: ~s0~%" response)
             (mv nil `(defconst *demo-agent-v6* 
                        (add-assistant-msg ,response *demo-agent-v5*)) 
                 state)))))

#-skip-interactive
(defconst *show-v6*
  (show-conversation *demo-agent-v6*))

;;;============================================================================
;;; Context Usage Check
;;;============================================================================

#-skip-interactive
(defconst *context-check*
  (show-context-usage *demo-agent-v6*))

;;;============================================================================
;;; Tool Result Demonstration
;;;============================================================================

#-skip-interactive
(defconst *demo-agent-with-tool*
  (add-tool-result 
    "File contents of verified-agent.lisp (first 500 chars):
; Verified ReAct Agent - ACL2 Implementation
; This file implements a formally verified ReAct agent...
(in-package \"ACL2\")
(include-book \"std/util/define\" :dir :system)
..." 
    *demo-agent-v6*))

#-skip-interactive
(defconst *show-tool*
  (show-conversation *demo-agent-with-tool*))

;;;============================================================================
;;; ReAct Step Demonstration
;;;============================================================================

(defconst *read-file-tool*
  (make-tool-spec
    :name 'read-file
    :required-access 1
    :requires-execute nil
    :token-cost 100
    :time-cost 5))

#-skip-interactive
(defconst *can-read-file*
  (prog2$ (cw "~%Can invoke read-file tool: ~x0~%" 
              (can-invoke-tool-p *read-file-tool* *demo-agent-v6*))
          (can-invoke-tool-p *read-file-tool* *demo-agent-v6*)))

#-skip-interactive
(defconst *demo-agent-after-react*
  (if (and (not (must-respond-p *demo-agent-v6*))
           (can-invoke-tool-p *read-file-tool* *demo-agent-v6*))
      (react-step-with-conversation
        (agent-action-tool-call 'read-file "verified-agent.lisp")
        *read-file-tool*
        "I'll read the verified-agent.lisp file to show you the implementation."
        "File read successfully. Contents: (in-package ACL2)..."
        *demo-agent-v6*)
    *demo-agent-v6*))

#-skip-interactive
(defconst *show-react*
  (prog2$ (cw "~%After ReAct step:~%")
    (prog2$ (cw "  Step counter: ~x0~%" 
                (agent-state->step-counter *demo-agent-after-react*))
      (prog2$ (cw "  Token budget: ~x0~%" 
                  (agent-state->token-budget *demo-agent-after-react*))
        (cw "  Message count: ~x0~%" 
            (len (get-messages *demo-agent-after-react*)))))))

;;;============================================================================
;;; Summary
;;;============================================================================

#-skip-interactive
(defconst *demo-complete*
  (prog2$ (cw "~%~%========================================~%")
    (prog2$ (cw "Chat Demo Complete!~%")
      (prog2$ (cw "========================================~%")
        (prog2$ (cw "~%Key points demonstrated:~%")
          (prog2$ (cw "  1. Agent state initialization~%")
            (prog2$ (cw "  2. Conversation management (add-user-msg, add-assistant-msg)~%")
              (prog2$ (cw "  3. Context length tracking~%")
                (prog2$ (cw "  4. Tool result handling~%")
                  (prog2$ (cw "  5. ReAct step with conversation~%")
                    (prog2$ (cw "~%For interactive chat, use chat.lisp instead:~%")
                      (prog2$ (cw "  (ld \"chat.lisp\")~%")
                        (cw "  (chat \"your message\")~%")))))))))))))
