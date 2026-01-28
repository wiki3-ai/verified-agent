; Chat - Interactive Chat Interface
; ==================================
; Load this file, then use (chat "your message") to interact.
;
; Usage:
;   cd src
;   acl2
;   (ld "chat.lisp")
;   (chat "Hello!")
;   (chat "Can you compute factorial of 5?")
;   (chat-reset)  ; to start fresh

(in-package "ACL2")

(include-book "chat-lib"
              :ttags ((:quicklisp) (:quicklisp.osicat) (:quicklisp.dexador) 
                      (:http-json) (:llm-client) (:mcp-client)))

;; Session is ready - use (chat "...") to interact
