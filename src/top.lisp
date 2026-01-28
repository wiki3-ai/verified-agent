; top.lisp - Certify all books in verified-agent
;
; Usage: cert.pl src/top
;        or: $ACL2_SYSTEM_BOOKS/build2/cert2 src/top

(in-package "ACL2")

;; Core types and decision functions (pure, no ttags)
(include-book "verified-agent")
(include-book "context-manager")
(include-book "llm-types")

;; HTTP and MCP clients
(include-book "http-json" :ttags (:quicklisp :quicklisp.dexador :http-json))
(include-book "llm-client" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client))
(include-book "mcp-client" :ttags (:quicklisp :quicklisp.dexador :http-json :mcp-client))

;; Utilities
(include-book "parinfer-fixer" :ttags (:parinfer-fixer))

;; Chat functionality
(include-book "chat" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client :mcp-client))
(include-book "chat-lib" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client :mcp-client))
(include-book "chat-openai" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client :mcp-client))

;; Top-level applications
(include-book "agent-runner" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client :mcp-client :parinfer))
(include-book "chat-demo" :ttags (:quicklisp :quicklisp.dexador :http-json :llm-client :mcp-client :parinfer-fixer))
