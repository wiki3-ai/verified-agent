# CLAUDE.md - Context for AI Assistants

This is the ACL2 Verified Agent project - a formally verified ReAct agent in ACL2.

## Quick Reference

### What This Is
- Formally verified AI agent decision logic in ACL2
- Uses FTY types for clean type definitions
- Integrates with LLMs via LM Studio
- Executes code via MCP protocol

### Key Commands
```bash
# Certify the main book
cd src && cert.pl verified-agent.lisp

# Run interactive demo (requires LM Studio)
acl2
(ld "chat-demo.lisp")
```

### File Locations
- **Source code**: `src/`
- **Main agent**: `src/verified-agent.lisp`
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
