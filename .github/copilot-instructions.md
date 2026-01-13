# Copilot Instructions for ACL2 Verified Agent

## Project Overview

A formally verified ReAct agent implemented in ACL2 with FTY types. The agent's decision logic is proven correct—external tools (knowledge graphs, vector stores, LLMs) are accessed via MCP and treated as oracles with bounded-response axioms.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
├─────────────────────────────────────────────────────────────────┤
│  Layer 5: Theorems                                              │
│  ├── permission-safety, budget-bounds-after-deduct              │
│  ├── termination-by-max-steps, continue-respond-partition       │
│  ├── conversation preservation theorems                         │
│  └── truncate-preserves-system-prompt                           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: ReAct Loop with Conversation                          │
│  ├── react-step (single iteration)                              │
│  ├── react-step-with-conversation (state + messages)            │
│  └── remaining-steps (termination measure)                      │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: State Transitions                                     │
│  ├── increment-step, deduct-tool-cost                           │
│  ├── update-satisfaction, mark-done, set-error                  │
│  └── add-user-msg, add-assistant-msg, add-tool-result           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: Context Management (context-manager.lisp)             │
│  ├── Token estimation (4 chars/token conservative)              │
│  ├── truncate-to-fit (sliding window, preserves system)         │
│  ├── truncate-output (head+tail for tool results)               │
│  └── add-message with automatic truncation                      │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: Pure Decision Functions                               │
│  ├── can-invoke-tool-p (permission + budget)                    │
│  ├── must-respond-p (termination conditions)                    │
│  └── should-continue-p (has budget, not satisfied)              │
├─────────────────────────────────────────────────────────────────┤
│  Layer 0: FTY Types                                             │
│  ├── agent-state, tool-spec, agent-action, error-kind           │
│  └── chat-role, chat-message, chat-message-list                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ MCP Protocol
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    External Tools (MCP)                         │
├─────────────────────────────────────────────────────────────────┤
│  acl2-mcp        │  LLM              │  Future: KG, Vector      │
│  (Code execution)│  (Language Model) │  (Oxigraph, Qdrant)      │
└─────────────────────────────────────────────────────────────────┘
```

## Directory Structure

```
verified-agent/
├── src/                    # ACL2 source files
│   ├── verified-agent.lisp # Core types, decision functions, safety theorems
│   ├── context-manager.lisp# Conversation history with sliding window truncation
│   ├── llm-types.lisp      # FTY types for chat messages
│   ├── llm-client.lisp     # HTTP client for LM Studio
│   ├── llm-client-raw.lsp  # Raw Lisp JSON serialization
│   ├── http-json.lisp      # HTTP POST/GET with JSON
│   ├── http-json-raw.lsp   # Raw Lisp HTTP implementation
│   ├── mcp-client.lisp     # MCP JSON-RPC client
│   ├── mcp-client-raw.lsp  # Raw Lisp MCP serialization
│   ├── agent-runner.lisp   # Runtime driver for code execution agent
│   ├── parinfer-fixer.lisp # Fix unbalanced parens in LLM output
│   └── chat-demo.lisp      # Interactive demo
├── acl2-mcp/               # Python MCP server for ACL2
│   ├── acl2_mcp/           # Python package
│   │   ├── __init__.py
│   │   └── server.py       # MCP server implementation
│   └── pyproject.toml      # Python project config
├── .devcontainer/          # Dev container config
└── .github/
    └── copilot-instructions.md
```

## Design Principles

1. **Verify the decision logic, not the world** — ACL2 proves properties about how the agent decides
2. **Keep verified core simple** — Complex operations (LLM, code execution) handled by external driver
3. **FTY over STObj** — Cleaner types, auto-generated theorems, easier reasoning
4. **MCP for external tools** — acl2-mcp provides code execution, future: Oxigraph, Qdrant
5. **Fix LLM output with parinfer** — Automatically correct unbalanced parens using indentation

## Key Files

| File | Purpose |
|------|---------|
| `verified-agent.lisp` | Main agent: FTY types, decision functions, safety theorems |
| `context-manager.lisp` | Conversation history with sliding window truncation |
| `llm-types.lisp` | FTY message types (chat-role, chat-message) |
| `llm-client.lisp` | HTTP client for LM Studio |
| `mcp-client.lisp` | MCP client with persistent ACL2 sessions |
| `agent-runner.lisp` | Runtime driver integrating all components + parinfer |
| `parinfer-fixer.lisp` | Parinfer integration for fixing LLM code output |
| `chat-demo.lisp` | Interactive ReAct demo with code execution |

## LLM Provider Configuration

The agent supports multiple LLM providers:

```lisp
;; Local (LM Studio - default)
(make-local-provider-config "model-name")

;; OpenAI (cloud)
(make-openai-provider-config "sk-your-api-key" "gpt-4o-mini")

;; Custom OpenAI-compatible endpoint
(make-custom-provider-config "https://api.example.com/v1/chat/completions" "api-key" "model")

;; Use provider in chat loop
(interactive-chat-loop-with-provider *initial-chat-state* config state)

;; Or single completion
(llm-chat-completion-with-provider config messages state)
```

LLM calls go to configured provider (default: LM Studio on host `http://host.docker.internal:1234/v1`).

## Permission Model

```lisp
;; File access levels (orthogonal to execute)
*access-none* = 0
*access-read* = 1  
*access-read-write* = 2

;; Decision functions
(tool-permitted-p tool st)        ; permission check
(tool-budget-sufficient-p tool st) ; budget check
(can-invoke-tool-p tool st)       ; permission AND budget
(must-respond-p st)               ; termination conditions
(should-continue-p st)            ; has budget, not satisfied
```

## Proven Safety Properties

- `permission-safety` — `can-invoke-tool-p → tool-permitted-p`
- `budget-bounds-after-deduct` — Budgets remain non-negative
- `termination-by-max-steps` — Agent halts within max-steps
- `truncate-preserves-system-prompt` — System message always preserved

## ACL2 File Conventions

- **Package declaration**: Every `.lisp` file starts with `(in-package "ACL2")`
- **File naming**: Descriptive names like `verified-agent.lisp`, `context-manager.lisp`
- **Helper lemmas**: Wrap with `(local ...)` to prevent export from book
- **Dependencies**: Use `(include-book "path/to/book")` for imports

## Key Build Commands

```bash
# Certify a specific book
cert.pl src/verified-agent.lisp

# Clean and recertify
rm -f src/*.cert src/*.cert.out src/*.lx64fsl && cert.pl src/verified-agent.lisp
```

## Critical ACL2 Patterns

### FTY Case Macros Require Variables

```lisp
;; WRONG - causes macro expansion error
(chat-role-case (chat-message->role msg) :system ...)

;; CORRECT - bind to variable first
(let ((role (chat-message->role msg)))
  (chat-role-case role :system ...))
```

### Guard Verification with Type-Prescription

```lisp
;; Return-type theorems need :type-prescription for guard verification
(defthm natp-of-my-fn
  (natp (my-fn x))
  :rule-classes (:rewrite :type-prescription))

;; Then disable definition in caller's guard hints
(defun caller (x)
  (declare (xargs :guard-hints (("Goal" :in-theory (disable my-fn)))))
  ...)
```

### Theory Control

```lisp
;; Disable rules that cause loops, enable at specific subgoals
:hints (("Goal" :in-theory (e/d (foo) (bar)))
        ("Subgoal *1/3" :in-theory (enable bar)))
```

## Common Predicates

- `(natp x)` - natural number, `(zp x)` - zero predicate
- `(true-listp l)` - proper list, `(stringp s)` - string
- `(consp x)` - non-empty list, `(endp x)` - end of list
- `(booleanp x)` - boolean, `(symbolp x)` - symbol

## Development Workflow

1. Write functions and theorems in `.lisp` file
2. Test interactively with acl2-mcp tools
3. If proof fails, check "key checkpoints" in output
4. Add local helper lemmas as stepping stones
5. Run `cert.pl file.lisp` to verify

## Testing with acl2-mcp

```bash
# Start mcp-proxy (required for tests)
mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment

# Use MCP tools for interactive testing
```

```lisp
;; In ACL2, use MCP functions
(mcp-acl2-evaluate conn "(+ 1 2)")           ; => 3
(mcp-acl2-admit conn "(defun foo (x) x)")    ; test without saving
(mcp-acl2-prove conn "(defthm ...)")         ; prove theorem
```

## Parinfer Integration

The agent uses [parinfer-rust](https://github.com/eraserhd/parinfer-rust) to fix unbalanced parentheses in LLM-generated code. Parinfer's "indent mode" infers correct parentheses from indentation, which is ideal since LLMs typically get indentation right but parens wrong.

```bash
# Install parinfer-rust
make install-parinfer

# Test installation
make test-parinfer

# Manual usage
echo '(defun foo (x)
  (+ x 1' | parinfer-rust -m indent --lisp-block-comments
# Output: (defun foo (x)
#           (+ x 1))
```

