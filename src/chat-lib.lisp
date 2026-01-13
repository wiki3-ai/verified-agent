; Chat Library - Common definitions for interactive chat
; =====================================================
; This file provides the core functions for running a ReAct agent
; with LLM and code execution support.
;
; Usage:
;   (include-book "chat-lib" :ttags ...)
;   Then use interactive-chat-loop or build your own chat flow.

(in-package "ACL2")

;;;============================================================================
;;; Dependencies
;;;============================================================================

(include-book "verified-agent")
(include-book "llm-client"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) (:http-json) (:llm-client)))
(include-book "mcp-client"
              :ttags ((:quicklisp) (:quicklisp.dexador) (:http-json) (:mcp-client)))

;;;============================================================================
;;; Configuration Constants
;;;============================================================================

;; Model preferences in order - first match wins
(defconst *model-prefs* '("qwen" "nemotron" "llama" "gemma"))

;; Default system prompt for the ReAct agent
(defconst *default-system-prompt*
  "You are a helpful AI assistant running inside a formally verified ReAct agent framework built in ACL2.

You have access to ACL2 code execution. To run ACL2 code, put it in a fenced code block:

```acl2
(+ 1 2 3)
```

or:

```lisp
(defun factorial (n) (if (zp n) 1 (* n (factorial (1- n)))))
```

I will execute the code and show you the result. You can then continue reasoning or give a final answer.

Be concise. Show your reasoning.")

;; Default agent configuration
(defconst *default-agent-config*
  (make-agent-state 
    :max-steps 20              ; Allow up to 20 conversation turns
    :token-budget 50000        ; Token budget for tool calls
    :time-budget 3600          ; 1 hour time budget
    :file-access 1             ; Read access to files
    :execute-allowed t         ; Code execution enabled
    :max-context-tokens 8000   ; Context window size
    :satisfaction 0))          ; Starting satisfaction

;;;============================================================================
;;; Provider Configuration Helpers
;;;============================================================================

;; Create OpenAI provider config from environment variable or parameter
(defun make-openai-provider-config (api-key model)
  "Create OpenAI provider configuration.
   API-KEY: Your OpenAI API key
   MODEL: Model name (e.g., \"gpt-4o-mini\", \"gpt-4o\", \"gpt-4-turbo\")"
  (declare (xargs :guard (and (stringp api-key) (stringp model))))
  (make-llm-provider-config
   :provider (llm-provider-openai)
   :endpoint "https://api.openai.com/v1/chat/completions"
   :api-key api-key
   :model model
   :org-id ""))

;; Create local LM Studio provider config
(defun make-local-provider-config (model)
  "Create local LM Studio provider configuration.
   MODEL: Model identifier from LM Studio"
  (declare (xargs :guard (stringp model)))
  (make-llm-provider-config
   :provider (llm-provider-local)
   :endpoint "http://host.docker.internal:1234/v1/chat/completions"
   :api-key ""
   :model model
   :org-id ""))

;; Create custom OpenAI-compatible provider config
(defun make-custom-provider-config (endpoint api-key model)
  "Create custom OpenAI-compatible provider configuration.
   ENDPOINT: API endpoint URL
   API-KEY: API key (empty string if not needed)
   MODEL: Model identifier"
  (declare (xargs :guard (and (stringp endpoint) 
                              (stringp api-key) 
                              (stringp model))))
  (make-llm-provider-config
   :provider (llm-provider-custom)
   :endpoint endpoint
   :api-key api-key
   :model model
   :org-id ""))

;;;============================================================================
;;; Display Helpers
;;;============================================================================

;; Print a string with proper Unicode handling using princ$
;; ACL2's cw ~s directive doesn't handle multi-byte UTF-8 well
(defun print-string (str state)
  "Print a string with proper Unicode support."
  (declare (xargs :mode :program :stobjs state))
  (princ$ str *standard-co* state))

(defun print-newline (state)
  "Print a newline."
  (declare (xargs :mode :program :stobjs state))
  (newline *standard-co* state))

(defun print-labeled (label str state)
  "Print a labeled string with newline, handling Unicode properly."
  (declare (xargs :mode :program :stobjs state))
  (let ((state (print-newline state)))
    (let ((state (print-string label state)))
      (let ((state (print-string str state)))
        (print-newline state)))))

(defun show-messages (msgs)
  "Display a list of chat messages."
  (declare (xargs :mode :program))
  (if (endp msgs)
      nil
    (let* ((msg (car msgs))
           (role (chat-message->role msg))
           (content (chat-message->content msg))
           (role-str (chat-role-case role
                       :system "SYSTEM"
                       :user "USER"
                       :assistant "ASSISTANT"
                       :tool "TOOL")))
      (prog2$ (cw "~%[~s0]~%~s1~%" role-str content)
              (show-messages (cdr msgs))))))

(defun show-conversation (st)
  "Display the full conversation from an agent state."
  (declare (xargs :mode :program))
  (prog2$ (cw "~%========== Conversation ==========")
          (prog2$ (show-messages (get-messages st))
                  (cw "~%===================================~%"))))

(defun show-context-usage (st)
  "Display context token usage statistics."
  (declare (xargs :mode :program))
  (let* ((msgs (get-messages st))
         (char-len (messages-char-length msgs))
         (token-est (messages-token-estimate msgs))
         (max-tokens (agent-state->max-context-tokens st)))
    (prog2$ (cw "~%Context Usage:~%")
      (prog2$ (cw "  Total characters: ~x0~%" char-len)
        (prog2$ (cw "  Estimated tokens: ~x0~%" token-est)
          (prog2$ (cw "  Max tokens: ~x0~%" max-tokens)
            (cw "  Fits in context: ~x0~%" 
                (messages-fit-p msgs max-tokens))))))))

;;;============================================================================
;;; Code Execution Support
;;;============================================================================

;; Strip leading whitespace from character list
(defun strip-leading-ws (lst)
  (declare (xargs :mode :program))
  (if (endp lst) nil
    (if (member (car lst) '(#\Space #\Tab #\Newline #\Return))
        (strip-leading-ws (cdr lst))
      lst)))

;; Trim whitespace from string
(defun my-string-trim (str)
  (declare (xargs :mode :program))
  (let* ((chars (coerce str 'list))
         (trimmed (strip-leading-ws chars))
         (rev-trimmed (strip-leading-ws (reverse trimmed))))
    (coerce (reverse rev-trimmed) 'string)))

;; Extract first ```acl2 or ```lisp code block from text
(defun extract-code-block (response)
  "Extract the first ACL2/Lisp code block from a response string."
  (declare (xargs :mode :program))
  (let* ((acl2-start (search "```acl2" response))
         (lisp-start (search "```lisp" response))
         (start-marker (cond ((and acl2-start lisp-start)
                              (if (< acl2-start lisp-start) "```acl2" "```lisp"))
                             (acl2-start "```acl2")
                             (lisp-start "```lisp")
                             (t nil)))
         (start-pos (cond ((and acl2-start lisp-start)
                           (min acl2-start lisp-start))
                          (acl2-start acl2-start)
                          (lisp-start lisp-start)
                          (t nil))))
    (if (not start-pos)
        (mv nil "")
      (let* ((content-start (+ start-pos (length start-marker)))
             (newline-pos (search (coerce '(#\Newline) 'string)
                                  (subseq response content-start (length response))))
             (code-start (if newline-pos (+ content-start newline-pos 1) content-start))
             (rest (subseq response code-start (length response)))
             (end-pos (search "```" rest)))
        (if (not end-pos)
            (mv nil "")
          (mv t (my-string-trim (subseq rest 0 end-pos))))))))

;; Execute ACL2 code via MCP
(defun execute-acl2-code (code mcp-conn state)
  "Execute ACL2 code via MCP connection."
  (declare (xargs :mode :program :stobjs state))
  (if (not (mcp-connection-p mcp-conn))
      (mv "No MCP connection" "" state)
    (mcp-acl2-execute mcp-conn code state)))

;;;============================================================================
;;; ReAct Loop Implementation
;;;============================================================================

(defun react-loop (agent-st model-id mcp-conn max-steps state)
  "Execute ReAct loop: LLM -> extract code -> execute -> repeat until no code block"
  (declare (xargs :mode :program :stobjs state))
  (if (zp max-steps)
      (prog2$ (cw "~%[Max steps reached]~%")
              (mv agent-st state))
    (mv-let (err response state)
      (llm-chat-completion model-id (get-messages agent-st) state)
      (if err
          (prog2$ (cw "~%LLM Error: ~s0~%" err)
                  (mv agent-st state))
        (let ((agent-st (add-assistant-msg response agent-st)))
          (prog2$ (cw "~%Assistant: ~s0~%" response)
            (mv-let (found? code)
              (extract-code-block response)
              (if (not found?)
                  ;; No code block - done with this turn
                  (mv agent-st state)
                ;; Execute code and continue
                (prog2$ (cw "~%[Executing: ~s0]~%" code)
                  (mv-let (exec-err result state)
                    (execute-acl2-code code mcp-conn state)
                    (let* ((tool-result (if exec-err
                                            (concatenate 'string "Error: " exec-err)
                                          result))
                           ;; Truncate long results for display
                           (display-result (if (> (length tool-result) 300)
                                               (concatenate 'string 
                                                 (subseq tool-result 0 300) "...")
                                             tool-result))
                           (agent-st (add-tool-result tool-result agent-st)))
                      (prog2$ (cw "~%Result: ~s0~%" display-result)
                        ;; Continue ReAct loop
                        (react-loop agent-st model-id mcp-conn (1- max-steps) state)))))))))))))

;; Provider-aware ReAct loop
(defun react-loop-with-provider (agent-st provider-config mcp-conn max-steps state)
  "Execute ReAct loop using provider config: LLM -> extract code -> execute -> repeat"
  (declare (xargs :mode :program :stobjs state))
  (if (zp max-steps)
      (prog2$ (cw "~%[Max steps reached]~%")
              (mv agent-st state))
    (mv-let (err response state)
      (llm-chat-completion-with-provider provider-config (get-messages agent-st) state)
      (if err
          (prog2$ (cw "~%LLM Error: ~s0~%" err)
                  (mv agent-st state))
        (let ((agent-st (add-assistant-msg response agent-st)))
          ;; Use princ$ for Unicode-safe output
          (let* ((state (print-newline state))
                 (state (print-string "Assistant: " state))
                 (state (print-string response state))
                 (state (print-newline state)))
            (mv-let (found? code)
              (extract-code-block response)
              (if (not found?)
                  ;; No code block - done with this turn
                  (mv agent-st state)
                ;; Execute code and continue
                (prog2$ (cw "~%[Executing: ~s0]~%" code)
                  (mv-let (exec-err result state)
                    (execute-acl2-code code mcp-conn state)
                    (let* ((tool-result (if exec-err
                                            (concatenate 'string "Error: " exec-err)
                                          result))
                           ;; Truncate long results for display
                           (display-result (if (> (length tool-result) 300)
                                               (concatenate 'string 
                                                 (subseq tool-result 0 300) "...")
                                             tool-result))
                           (agent-st (add-tool-result tool-result agent-st)))
                      (prog2$ (cw "~%Result: ~s0~%" display-result)
                        ;; Continue ReAct loop
                        (react-loop-with-provider agent-st provider-config mcp-conn 
                                                  (1- max-steps) state)))))))))))))

(defun chat-turn (user-msg agent-st model-id mcp-conn state)
  "Execute one chat turn with ReAct: add user message, run ReAct loop"
  (declare (xargs :mode :program :stobjs state))
  (let ((st-with-user (add-user-msg user-msg agent-st)))
    (react-loop st-with-user model-id mcp-conn 5 state)))

;; Provider-aware chat turn
(defun chat-turn-with-provider (user-msg agent-st provider-config mcp-conn state)
  "Execute one chat turn with provider config: add user message, run ReAct loop"
  (declare (xargs :mode :program :stobjs state))
  (let ((st-with-user (add-user-msg user-msg agent-st)))
    (react-loop-with-provider st-with-user provider-config mcp-conn 5 state)))

;;;============================================================================
;;; Completions API ReAct Loop (for Codex models)
;;;============================================================================

;; Completions-aware ReAct loop for models like Codex that use /v1/completions
(defun react-loop-with-completions (agent-st provider-config mcp-conn max-steps max-tokens state)
  "Execute ReAct loop using completions API: LLM -> extract code -> execute -> repeat.
   For Codex and other models that use /v1/completions instead of chat API."
  (declare (xargs :mode :program :stobjs state))
  (if (zp max-steps)
      (prog2$ (cw "~%[Max steps reached]~%")
              (mv agent-st state))
    (mv-let (err response state)
      (llm-completions-with-provider provider-config (get-messages agent-st) max-tokens state)
      (if err
          (prog2$ (cw "~%LLM Error: ~s0~%" err)
                  (mv agent-st state))
        (let ((agent-st (add-assistant-msg response agent-st)))
          (prog2$ (cw "~%Assistant: ~s0~%" response)
            (mv-let (found? code)
              (extract-code-block response)
              (if (not found?)
                  ;; No code block - done with this turn
                  (mv agent-st state)
                ;; Execute code and continue
                (prog2$ (cw "~%[Executing: ~s0]~%" code)
                  (mv-let (exec-err result state)
                    (execute-acl2-code code mcp-conn state)
                    (let* ((tool-result (if exec-err
                                            (concatenate 'string "Error: " exec-err)
                                          result))
                           ;; Truncate long results for display
                           (display-result (if (> (length tool-result) 300)
                                               (concatenate 'string 
                                                 (subseq tool-result 0 300) "...")
                                             tool-result))
                           (agent-st (add-tool-result tool-result agent-st)))
                      (prog2$ (cw "~%Result: ~s0~%" display-result)
                        ;; Continue ReAct loop
                        (react-loop-with-completions agent-st provider-config mcp-conn 
                                                     (1- max-steps) max-tokens state)))))))))))))

;; Completions-aware chat turn
(defun chat-turn-with-completions (user-msg agent-st provider-config mcp-conn max-tokens state)
  "Execute one chat turn with completions API: add user message, run ReAct loop"
  (declare (xargs :mode :program :stobjs state))
  (let ((st-with-user (add-user-msg user-msg agent-st)))
    (react-loop-with-completions st-with-user provider-config mcp-conn 5 max-tokens state)))

;;;============================================================================
;;; Input Reading
;;;============================================================================

(defun read-line-chars (acc state)
  "Accumulate characters until newline or EOF."
  (declare (xargs :mode :program :stobjs state))
  (mv-let (char state)
    (read-char$ *standard-ci* state)
    (cond ((null char)  ; EOF
           (mv (if (null acc) nil (coerce (reverse acc) 'string)) state))
          ((eql char #\Newline)
           (mv (coerce (reverse acc) 'string) state))
          (t (read-line-chars (cons char acc) state)))))

(defun read-line-from-user (state)
  "Read a line from standard input, return (mv line state)."
  (declare (xargs :mode :program :stobjs state))
  (read-line-chars nil state))

;;;============================================================================
;;; Interactive Chat Loop
;;;============================================================================

(defun interactive-chat-loop-aux (agent-st model-id mcp-conn state)
  "Helper for interactive chat loop with code execution."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ")
    (mv-let (input state)
      (read-line-from-user state)
      (if (or (null input)
              (equal input "/exit")
              (equal input "/quit"))
          (prog2$ (cw "~%Goodbye!~%")
                  (mv agent-st state))
        (mv-let (new-agent state)
          (chat-turn input agent-st model-id mcp-conn state)
          (interactive-chat-loop-aux new-agent model-id mcp-conn state))))))

;; Provider-aware interactive chat loop helper
(defun interactive-chat-loop-with-provider-aux (agent-st provider-config mcp-conn state)
  "Helper for interactive chat loop with provider config and code execution."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ")
    (mv-let (input state)
      (read-line-from-user state)
      (if (or (null input)
              (equal input "/exit")
              (equal input "/quit"))
          (prog2$ (cw "~%Goodbye!~%")
                  (mv agent-st state))
        (mv-let (new-agent state)
          (chat-turn-with-provider input agent-st provider-config mcp-conn state)
          (interactive-chat-loop-with-provider-aux new-agent provider-config mcp-conn state))))))

(defun interactive-chat-loop (agent-st model-id state)
  "Run an interactive ReAct chat loop with code execution. Type /exit to quit."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%========================================~%")
    (prog2$ (cw "Interactive ReAct Chat with Code Execution~%")
      (prog2$ (cw "(type /exit to quit)~%")
        (prog2$ (cw "========================================~%")
          (prog2$ (cw "~%Connecting to MCP server...~%")
            (mv-let (mcp-err mcp-conn state)
              (mcp-connect *mcp-default-endpoint* state)
              (if mcp-err
                  (prog2$ (cw "MCP connection failed: ~s0~%" mcp-err)
                    (prog2$ (cw "Code execution disabled.~%")
                      (interactive-chat-loop-aux agent-st model-id nil state)))
                (prog2$ (cw "MCP connected.~%")
                  (prog2$ (if (mcp-connection-has-acl2-session-p mcp-conn)
                              (cw "ACL2 session: ~s0~%" 
                                  (mcp-connection->acl2-session-id mcp-conn))
                            (cw "Warning: No persistent ACL2 session (slower mode).~%"))
                    (interactive-chat-loop-aux agent-st model-id mcp-conn state)))))))))))

;; Provider-aware interactive chat loop
(defun interactive-chat-loop-with-provider (agent-st provider-config state)
  "Run an interactive ReAct chat loop with cloud/local provider. Type /exit to quit.
   
   Example usage with OpenAI:
     (interactive-chat-loop-with-provider 
       *initial-chat-state*
       (make-openai-provider-config \"sk-...\" \"gpt-4o-mini\")
       state)
   
   Example usage with local LM Studio:
     (interactive-chat-loop-with-provider 
       *initial-chat-state*
       (make-local-provider-config \"qwen2.5-coder-7b\")
       state)"
  (declare (xargs :mode :program :stobjs state))
  (let ((provider-name (llm-provider-to-string 
                        (llm-provider-config->provider provider-config)))
        (model-name (llm-provider-config->model provider-config)))
    (prog2$ (cw "~%========================================~%")
      (prog2$ (cw "Interactive ReAct Chat with ~s0~%" (string-upcase provider-name))
        (prog2$ (cw "Model: ~s0~%" model-name)
          (prog2$ (cw "(type /exit to quit)~%")
            (prog2$ (cw "========================================~%")
              (prog2$ (cw "~%Connecting to MCP server...~%")
                (mv-let (mcp-err mcp-conn state)
                  (mcp-connect *mcp-default-endpoint* state)
                  (if mcp-err
                      (prog2$ (cw "MCP connection failed: ~s0~%" mcp-err)
                        (prog2$ (cw "Code execution disabled.~%")
                          (interactive-chat-loop-with-provider-aux 
                           agent-st provider-config nil state)))
                    (prog2$ (cw "MCP connected.~%")
                      (prog2$ (if (mcp-connection-has-acl2-session-p mcp-conn)
                                  (cw "ACL2 session: ~s0~%" 
                                      (mcp-connection->acl2-session-id mcp-conn))
                                (cw "Warning: No persistent ACL2 session (slower mode).~%"))
                        (interactive-chat-loop-with-provider-aux 
                         agent-st provider-config mcp-conn state)))))))))))))

;; Completions-aware interactive chat loop helper (for Codex models)
(defun interactive-chat-loop-with-completions-aux (agent-st provider-config max-tokens mcp-conn state)
  "Helper for interactive chat loop with completions API and code execution."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ")
    (mv-let (input state)
      (read-line-from-user state)
      (if (or (null input)
              (equal input "/exit")
              (equal input "/quit"))
          (prog2$ (cw "~%Goodbye!~%")
                  (mv agent-st state))
        (mv-let (new-agent state)
          (chat-turn-with-completions input agent-st provider-config mcp-conn max-tokens state)
          (interactive-chat-loop-with-completions-aux new-agent provider-config max-tokens mcp-conn state))))))

;; Completions-aware interactive chat loop (for Codex models)
(defun interactive-chat-loop-with-completions (agent-st provider-config max-tokens state)
  "Run an interactive ReAct chat loop using completions API (for Codex models).
   Type /exit to quit.
   
   Example usage with OpenAI Codex:
     (interactive-chat-loop-with-completions
       *initial-chat-state*
       (make-openai-provider-config \"sk-...\" \"gpt-5.1-codex\")
       2048  ; max tokens
       state)"
  (declare (xargs :mode :program :stobjs state))
  (let ((provider-name (llm-provider-to-string 
                        (llm-provider-config->provider provider-config)))
        (model-name (llm-provider-config->model provider-config)))
    (prog2$ (cw "~%========================================~%")
      (prog2$ (cw "Interactive ReAct Chat with ~s0 (Completions API)~%" (string-upcase provider-name))
        (prog2$ (cw "Model: ~s0~%" model-name)
          (prog2$ (cw "Max tokens: ~x0~%" max-tokens)
            (prog2$ (cw "(type /exit to quit)~%")
              (prog2$ (cw "========================================~%")
                (prog2$ (cw "~%Connecting to MCP server...~%")
                  (mv-let (mcp-err mcp-conn state)
                    (mcp-connect *mcp-default-endpoint* state)
                    (if mcp-err
                        (prog2$ (cw "MCP connection failed: ~s0~%" mcp-err)
                          (prog2$ (cw "Code execution disabled.~%")
                            (interactive-chat-loop-with-completions-aux 
                             agent-st provider-config max-tokens nil state)))
                      (prog2$ (cw "MCP connected.~%")
                        (prog2$ (if (mcp-connection-has-acl2-session-p mcp-conn)
                                    (cw "ACL2 session: ~s0~%" 
                                        (mcp-connection->acl2-session-id mcp-conn))
                                  (cw "Warning: No persistent ACL2 session (slower mode).~%"))
                          (interactive-chat-loop-with-completions-aux 
                           agent-st provider-config max-tokens mcp-conn state))))))))))))))

;;;============================================================================
;;; Session State Setup
;;;============================================================================

;; Initialize fresh agent state
(defconst *initial-chat-state*
  (init-agent-conversation *default-system-prompt* *default-agent-config*))

;;;============================================================================
;;; Chat Interface (skipped during certification)
;;; These define session state and the (chat "...") macro for interactive use.
;;;============================================================================

; cert_param: (cert_env "SKIP_INTERACTIVE=1")

#-skip-interactive
(make-event
 (mv-let (err models state)
   (llm-list-models-full state)
   (declare (ignorable err))
   (let* ((selected (select-completions-model models *model-prefs*))
          (model-id (if selected (model-info->id selected) "no-model-found")))
     (prog2$
      (if selected
          (cw "~%Selected model: ~s0 (context: ~x1 tokens)~%"
              model-id
              (model-info->loaded-context-length selected))
        (cw "~%WARNING: No model found. Ensure LM Studio is running.~%"))
      (mv nil `(defconst *chat-model* ,model-id) state)))))

#-skip-interactive
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
    (mv nil `(defconst *chat-mcp* ',mcp-conn) state))))

#-skip-interactive
(defconst *chat-agent* *initial-chat-state*)

#-skip-interactive
(defun chat-fn (msg state)
  "Send a message and get a response. Updates *chat-agent* state."
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "~%You: ~s0~%" msg)
    (mv-let (new-agent state)
      (chat-turn msg *chat-agent* *chat-model* *chat-mcp* state)
      (mv nil
          `(progn (redef+)
                  (defconst *chat-agent* ',new-agent)
                  (redef-))
          state))))

#-skip-interactive
(defmacro chat (msg)
  "Send a message to the chat agent. Example: (chat \"Hello!\")"
  `(make-event (chat-fn ,msg state)))

#-skip-interactive
(defmacro chat-reset ()
  "Reset the conversation to initial state."
  '(progn
     (redef+)
     (defconst *chat-agent* *initial-chat-state*)
     (redef-)
     (value-triple :chat-reset)))
