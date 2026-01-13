# CLAUDE.md - Context for AI Assistants

This is the ACL2 Verified Agent project - a formally verified ReAct agent in ACL2.

## Quick Reference

### What This Is
- Formally verified AI agent decision logic in ACL2
- Uses FTY types for clean type definitions
- Integrates with LLMs via local (LM Studio) or cloud (OpenAI) providers
- Executes code via MCP protocol
- Auto-fixes LLM paren errors with parinfer

### Key Commands
```bash
# Certify the main book
cd src && cert.pl verified-agent.lisp

# Run interactive demo (requires LM Studio)
acl2
(ld "chat-demo.lisp")

# Run with OpenAI (cloud provider)
acl2
(ld "chat-lib.lisp")
(defconst *openai-config* (make-openai-provider-config "sk-..." "gpt-4o-mini"))
(interactive-chat-loop-with-provider *initial-chat-state* *openai-config* state)

# Install parinfer for fixing LLM code
make install-parinfer
make test-parinfer
```

### LLM Provider Configuration
```lisp
;; Local (LM Studio)
(make-local-provider-config "model-name")

;; OpenAI
(make-openai-provider-config "sk-..." "gpt-4o-mini")

;; Custom OpenAI-compatible
(make-custom-provider-config "https://api.example.com/v1/chat/completions" "api-key" "model")
```

### File Locations
- **Source code**: `src/`
- **Main agent**: `src/verified-agent.lisp`
- **Parinfer fixer**: `src/parinfer-fixer.lisp`
- **MCP server**: `acl2-mcp/acl2_mcp/server.py`
- **Spec**: `src/Verified_Agent_Spec.md`
- **Copilot instructions**: `.github/copilot-instructions.md`

### Proven Properties
1. `permission-safety` - Can't invoke tools without permission
2. `budget-bounds-after-deduct` - Budgets stay non-negative
3. `termination-by-max-steps` - Agent halts within max-steps
4. `truncate-preserves-system-prompt` - System message survives truncation

### Important Patterns
- Use `(let ((var (accessor obj))) (case-macro var ...))` for FTY case macros
- Include `:type-prescription` for return-type theorems used in guards
- Use `(local ...)` for helper lemmas

### Parinfer Integration
The agent uses parinfer-rust to fix unbalanced parens in LLM output:
```bash
# Example: LLM generates code with missing parens
echo '(defun foo (x)
  (+ x 1' | parinfer-rust -m indent --lisp-block-comments
# Output: (defun foo (x)
#           (+ x 1))
```
