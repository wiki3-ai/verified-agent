# ACL2 Verified Agent

A formally verified ReAct agent implemented in ACL2 with FTY types. The agent's decision logic is mathematically proven correct, while external tools (LLMs, code execution) are accessed via the Model Context Protocol (MCP).

## What is This?

This project demonstrates how to build AI agents with **formally verified decision logic**:

- **Proven Safety**: ACL2 proves that the agent respects permissions, stays within budget, and terminates
- **Proven Correctness**: State transitions preserve invariants; context management preserves system prompts
- **Practical Integration**: Real LLM integration via LM Studio, code execution via MCP

## Features

- ✅ **FTY-typed agent state** with step counters, budgets, permissions, and conversation history
- ✅ **Permission model** with file access levels and code execution controls
- ✅ **Budget tracking** for tokens and time
- ✅ **Context management** with sliding window truncation that preserves system prompts
- ✅ **Proven termination** via max-steps bound
- ✅ **MCP integration** for ACL2 code execution with persistent sessions
- ✅ **LLM integration** via LM Studio's OpenAI-compatible API
- ✅ **Parinfer integration** to auto-fix unbalanced parens in LLM-generated code

## Proven Properties

All theorems are in [verified-agent.lisp](src/verified-agent.lisp) unless noted.

| Theorem | What It Proves |
|---------|----------------|
| `permission-safety` | Tool invocation requires permission |
| `budget-bounds-after-deduct` | Budgets remain non-negative |
| `termination-by-max-steps` | Agent halts within max-steps |
| `truncate-preserves-system-prompt` | System message survives truncation ([context-manager.lisp](src/context-manager.lisp)) |
| `error-state-forces-must-respond` | Internal errors (resource exhaustion, etc.) halt the agent |
| `add-tool-result-preserves-error-state` | Tool results don't change internal error state |
| `add-tool-result-preserves-has-error-p` | Tool results don't affect error status |
| `add-tool-result-preserves-done` | Tool results don't change done flag |
| `external-tool-call-bounded` | External tool responses have bounded length |

> **Note:** Tool execution errors are *not* internal errors—they are returned to the agent as messages so it can see and recover from them. The `add-tool-result-preserves-*` theorems prove this is safe. Only infrastructure failures (LLM unreachable, budget exhausted) halt the loop.

## Quick Start

### Prerequisites

- [VS Code](https://code.visualstudio.com/) with [Dev Containers extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
- [Docker](https://www.docker.com/)
- [LM Studio](https://lmstudio.ai/) (optional, for LLM integration)

### 1. Clone and Open in Dev Container

```bash
git clone https://github.com/YOUR_USERNAME/verified-agent.git
cd verified-agent
code .
# When prompted, click "Reopen in Container"
```

### 2. Certify the ACL2 Books

```bash
cd src
cert.pl verified-agent.lisp
```

### 3. Start acl2-mcp
```bash
pip install mcp-proxy
mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment
```

### 4. Run Interactive Demo (requires LM Studio)

Start LM Studio with a model loaded, then in ACL2:

```lisp
(ld "chat-demo.lisp")
(interactive-chat-loop *agent-v1* *model-id* state)
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Verified Agent (ACL2)                        │
│  Proven: permission-safety, budget-bounds, termination          │
├─────────────────────────────────────────────────────────────────┤
│  ReAct Loop: react-step → LLM → extract code → execute → loop   │
├─────────────────────────────────────────────────────────────────┤
│  Context Manager: truncate-to-fit preserves system prompt       │
├─────────────────────────────────────────────────────────────────┤
│  Decision Functions: can-invoke-tool-p, must-respond-p          │
├─────────────────────────────────────────────────────────────────┤
│  FTY Types: agent-state, tool-spec, chat-message, error-kind    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ MCP / HTTP
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  External Tools: acl2-mcp (code execution), LM Studio (LLM)     │
└─────────────────────────────────────────────────────────────────┘
```

## File Structure

```
verified-agent/
├── .devcontainer/
│   └── devcontainer.json       # Dev container config for ACL2 environment
├── .github/
│   └── copilot-instructions.md # AI assistant guidance
├── src/                        # ACL2 source files
│   ├── verified-agent.lisp     # Core: FTY types, decision functions, safety theorems
│   ├── context-manager.lisp    # Conversation history with truncation proofs
│   ├── llm-types.lisp          # FTY types for chat messages
│   ├── llm-client.lisp         # HTTP client for LM Studio
│   ├── llm-client-raw.lsp      # Raw Lisp JSON serialization
│   ├── http-json.lisp          # HTTP POST/GET with JSON
│   ├── http-json-raw.lsp       # Raw Lisp HTTP implementation
│   ├── mcp-client.lisp         # MCP JSON-RPC client
│   ├── mcp-client-raw.lsp      # Raw Lisp MCP serialization
│   ├── agent-runner.lisp       # Runtime driver for code execution
│   ├── parinfer-fixer.lisp     # Fix unbalanced parens in LLM output
│   ├── chat-demo.lisp          # Interactive demo
│   └── Verified_Agent_Spec.md  # Full specification
├── acl2-mcp/                   # Python MCP server
│   ├── acl2_mcp/
│   │   ├── __init__.py
│   │   └── server.py           # MCP server (15 tools for ACL2)
│   ├── pyproject.toml
│   ├── README.md
│   ├── LICENSE
│   └── SECURITY.md
├── .gitignore
├── CLAUDE.md                   # Quick context for AI assistants
├── LICENSE                     # BSD 3-Clause
├── Makefile                    # Build automation
└── README.md                   # This file
```

## How It Works

### The Agent State

```lisp
(fty::defprod agent-state
  ((step-counter natp :default 0)
   (max-steps natp :default 100)
   (token-budget natp :default 10000)
   (time-budget natp :default 3600)
   (file-access natp :default 0)          ; 0=none, 1=read, 2=write
   (execute-allowed booleanp :default nil)
   (messages chat-message-list-p :default nil)
   (satisfaction natp :default 0)
   (done booleanp :default nil)
   (error-state error-kind-p :default '(:none)))
  :layout :list)
```

### Decision Logic

The agent decides what to do based on pure functions:

```lisp
;; Can we invoke this tool?
(can-invoke-tool-p tool st) = (tool-permitted-p tool st) 
                             AND (tool-budget-sufficient-p tool st)

;; Must we stop?
(must-respond-p st) = done OR has-error OR (step-counter >= max-steps)
                      OR (token-budget = 0) OR (time-budget = 0)
```

### Code Execution via MCP

The agent can execute ACL2 code through the MCP protocol:

```lisp
;; LLM writes code in markdown blocks
;; ```acl2
;; (+ 1 2 3)
;; ```

;; Agent extracts and executes via MCP
(mcp-acl2-evaluate conn "(+ 1 2 3)")  ; => "6"
```

### Parinfer: Fixing LLM Code Errors

LLMs often generate Lisp code with unbalanced parentheses, even though the indentation is correct. The agent uses [parinfer-rust](https://github.com/eraserhd/parinfer-rust) to automatically fix these errors before execution:

```lisp
;; LLM output (missing closing parens):
(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (1- n)

;; After parinfer fix:
(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (1- n)))))
```

Install parinfer-rust:
```bash
make install-parinfer  # Installs Rust + parinfer-rust from GitHub
make test-parinfer     # Verify installation
```

## Development

### Running Tests

```bash
# Certify all books
cd src && cert.pl verified-agent.lisp

# Run MCP server tests
cd acl2-mcp && python -m pytest
```

### Starting MCP Server for Testing

```bash
# Via mcp-proxy for HTTP transport
mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment
```

## Design Philosophy

1. **Verify the decision logic, not the world** — ACL2 proves properties about how the agent *decides*, given any external responses
2. **FTY over STObj** — Cleaner types, auto-generated theorems, easier reasoning
3. **MCP for external tools** — Standard protocol for tool integration
4. **Keep verified core simple** — Complex I/O in external driver, proofs in ACL2
5. **Fix LLM output with parinfer** — Automatically correct unbalanced parens using indentation

## License

BSD 3-Clause License. See [LICENSE](LICENSE).

## Acknowledgments

- Built with [ACL2](https://www.cs.utexas.edu/users/moore/acl2/)
- LLM integration via [LM Studio](https://lmstudio.ai/)
- MCP implementation using [MCP Python SDK](https://github.com/modelcontextprotocol/python-sdk)
- Paren fixing via [parinfer-rust](https://github.com/eraserhd/parinfer-rust)
