# Makefile for ACL2 Verified Agent
# Includes ACL2 book certification and Jupyter notebook generation

.PHONY: all clean cert test notebooks clean-notebooks

# Path to the converter script
CONVERTER_SCRIPT := utils/lisp-to-ipynb.lisp
CONVERTER := sbcl --script $(CONVERTER_SCRIPT) --acl2

# Find all .lisp files in src directory
LISP_FILES := $(wildcard src/*.lisp)

# Generate corresponding .ipynb targets
NOTEBOOKS := $(LISP_FILES:.lisp=.ipynb)

# Default target: certify all books
all: certify-all

# Certify ACL2 books
certify-all: certify-community-books certify-src 

# Full certification including runtime
certify-src:
	cert.pl $(LISP_FILES)

# Generate Jupyter notebooks from .lisp files
notebooks: $(NOTEBOOKS)

# Pattern rule: how to build a .ipynb from a .lisp
%.ipynb: %.lisp $(CONVERTER_SCRIPT)
	@echo "Converting $< -> $@"
	$(CONVERTER) $<

# Clean all generated files (certs only)
clean:
	rm -f src/*.cert src/*.cert.out src/*.lx64fsl src/*.fasl src/*.port
	rm -f src/*.pcert0 src/*.pcert1 src/*.acl2x

# Clean generated notebooks
clean-notebooks:
	rm -f $(NOTEBOOKS)

# Clean everything
clean-all: clean clean-notebooks

# =============================================================================
# ACL2 Community Books used by this project
# =============================================================================
# The following community books are used (with :dir :system):
#
#   centaur/fty/top                          - FTY type definition library
#   std/util/define                          - Enhanced defun with contracts
#   std/util/bstar                           - B* binding macro
#   std/lists/top                            - List utilities
#   std/strings/top                          - String utilities
#   std/strings/cat                          - String concatenation
#   std/strings/explode-nonnegative-integer  - Integer to string conversion
#   quicklisp/dexador                        - HTTP client (via Quicklisp)
#   kestrel/json-parser/parse-json           - JSON parsing
#   kestrel/json-parser/parse-json-file      - JSON file parsing
#
# These are located under $ACL2_SYSTEM_BOOKS (typically acl2/books/)
# =============================================================================

# List of community books used by this project
COMMUNITY_BOOKS := \
	centaur/fty/top \
	std/util/define \
	std/util/bstar \
	std/lists/top \
	std/strings/top \
	std/strings/cat \
	std/strings/explode-nonnegative-integer \
	quicklisp/dexador \
	kestrel/json-parser/parse-json \
	kestrel/json-parser/parse-json-file

# Certify community books (run from ACL2 system books directory)
# Note: ACL2_SYSTEM_BOOKS should point to your ACL2 books directory
certify-community-books:
	@if [ -z "$$ACL2_SYSTEM_BOOKS" ]; then \
		echo "Error: ACL2_SYSTEM_BOOKS environment variable not set"; \
		echo "Set it to your ACL2 books directory, e.g.:"; \
		echo "  export ACL2_SYSTEM_BOOKS=/path/to/acl2/books"; \
		exit 1; \
	fi
	@echo "Certifying community books in $$ACL2_SYSTEM_BOOKS..."
	@for book in $(COMMUNITY_BOOKS); do \
		echo "Certifying $$book..."; \
		cd "$$ACL2_SYSTEM_BOOKS" && cert.pl "$$book.lisp" || exit 1; \
	done
	@echo "All community books certified successfully."

# Check if community books are already certified
check-community-books:
	@if [ -z "$$ACL2_SYSTEM_BOOKS" ]; then \
		echo "Error: ACL2_SYSTEM_BOOKS environment variable not set"; \
		exit 1; \
	fi
	@echo "Checking community book certifications..."
	@all_ok=true; \
	for book in $(COMMUNITY_BOOKS); do \
		if [ -f "$$ACL2_SYSTEM_BOOKS/$$book.cert" ]; then \
			echo "  ✓ $$book"; \
		else \
			echo "  ✗ $$book (not certified)"; \
			all_ok=false; \
		fi; \
	done; \
	if [ "$$all_ok" = true ]; then \
		echo "All community books are certified."; \
	else \
		echo "Some books need certification. Run: make cert-community-books"; \
	fi

# Run Python tests for acl2-mcp
test:
	cd acl2-mcp && python -m pytest -v

# Install Python dependencies
install-deps:
	pip install -e acl2-mcp

# =============================================================================
# ACL2 Bridge SBCL Port (from PR #1882)
# =============================================================================
# Merges the SBCL port of ACL2 Bridge from:
# https://github.com/acl2/acl2/pull/1882
#
# This adds support for running ACL2 Bridge on SBCL (in addition to CCL)

BRIDGE_PR_REPO := https://github.com/jimwhite/acl2.git
BRIDGE_PR_BRANCH := bridge2sbcl
BRIDGE_DIR := $(ACL2_SYSTEM_BOOKS)/centaur/bridge
BRIDGE_FILES := books/centaur/bridge/bridge-sbcl-raw.lsp books/centaur/bridge/top.lisp

# Download and install ACL2 Bridge SBCL files from PR #1882 using git
# Uses sparse checkout to fetch only the bridge directory
install-bridge-sbcl:
	@if [ -z "$$ACL2_SYSTEM_BOOKS" ]; then \
		echo "Error: ACL2_SYSTEM_BOOKS environment variable not set"; \
		echo "Set it to your ACL2 books directory, e.g.:"; \
		echo "  export ACL2_SYSTEM_BOOKS=/path/to/acl2/books"; \
		exit 1; \
	fi
	@echo "Installing ACL2 Bridge SBCL port from PR #1882..."
	@echo "Using sparse checkout to fetch bridge files..."
	@rm -rf /tmp/acl2-bridge-pr
	git clone --depth 1 --filter=blob:none --sparse \
		$(BRIDGE_PR_REPO) -b $(BRIDGE_PR_BRANCH) /tmp/acl2-bridge-pr
	cd /tmp/acl2-bridge-pr && git sparse-checkout set books/centaur/bridge
	@echo ""
	@echo "Copying files to $(BRIDGE_DIR)..."
	cp /tmp/acl2-bridge-pr/books/centaur/bridge/bridge-sbcl-raw.lsp "$(BRIDGE_DIR)/"
	cp /tmp/acl2-bridge-pr/books/centaur/bridge/top.lisp "$(BRIDGE_DIR)/"
	@echo "  ✓ bridge-sbcl-raw.lsp"
	@echo "  ✓ top.lisp"
	@rm -rf /tmp/acl2-bridge-pr
	cert.pl $(BRIDGE_DIR)/top.lisp
	@echo ""
	@echo "ACL2 Bridge SBCL port installed successfully!"


# Check if ACL2 Bridge SBCL files are installed
check-bridge-sbcl:
	@if [ -z "$$ACL2_SYSTEM_BOOKS" ]; then \
		echo "Error: ACL2_SYSTEM_BOOKS environment variable not set"; \
		exit 1; \
	fi
	@echo "Checking ACL2 Bridge SBCL installation..."
	@if [ -f "$(BRIDGE_DIR)/bridge-sbcl-raw.lsp" ]; then \
		echo "  ✓ bridge-sbcl-raw.lsp"; \
	else \
		echo "  ✗ bridge-sbcl-raw.lsp (not found)"; \
	fi
	@if grep -q "bridge-sbcl-raw.lsp" "$(BRIDGE_DIR)/top.lisp" 2>/dev/null; then \
		echo "  ✓ top.lisp (has SBCL support)"; \
	else \
		echo "  ✗ top.lisp (missing SBCL support)"; \
	fi

# Certify ACL2 Bridge (requires quicklisp books on SBCL)
certify-bridge:
	@if [ -z "$$ACL2_SYSTEM_BOOKS" ]; then \
		echo "Error: ACL2_SYSTEM_BOOKS environment variable not set"; \
		exit 1; \
	fi
	@echo "Certifying ACL2 Bridge..."
	cd "$(BRIDGE_DIR)" && cert.pl top.lisp

# =============================================================================
# Rust and Parinfer Setup
# =============================================================================

CARGO_ENV := $(HOME)/.cargo/env

# Source cargo environment - use this prefix for any cargo commands
# Note: Each make recipe runs in a new shell, so we must source in each command
CARGO := . "$(CARGO_ENV)" 2>/dev/null && 

# Install Rust toolchain if not present
install-rust:
	@if [ ! -f "$(CARGO_ENV)" ]; then \
		echo "Installing Rust toolchain..."; \
		curl https://sh.rustup.rs -sSf | sh -s -- -y; \
		echo ""; \
		echo "Rust installed. To use cargo in this shell, run:"; \
		echo "  source $(CARGO_ENV)"; \
	else \
		echo "Rust already installed at $(CARGO_ENV)"; \
	fi

# Install parinfer-rust CLI (not on crates.io, must use GitHub)
install-parinfer: install-rust
	@$(CARGO) \
	if command -v parinfer-rust >/dev/null 2>&1; then \
		echo "parinfer-rust already installed"; \
	else \
		echo "Installing parinfer-rust from GitHub..."; \
		cargo install --git https://github.com/eraserhd/parinfer-rust; \
	fi

# Test parinfer-rust installation  
test-parinfer:
	@$(CARGO) echo '(def x' | parinfer-rust -m indent
	@$(CARGO) echo '(defun foo (x)' | parinfer-rust -m indent --lisp-block-comments
	@echo "Parinfer tests passed!"

# Run a command with Rust/Cargo environment
# Usage: make cargo-run CMD="cargo --version"
cargo-run:
	@$(CARGO) $(CMD)

# Help
help:
	@echo "Available targets:"
	@echo "  all                   - Certify main ACL2 books (default)"
	@echo "  cert                  - Certify verified-agent.lisp"
	@echo "  cert-all              - Certify all books including runtime"
	@echo "  cert-community-books  - Certify all required ACL2 community books"
	@echo "  check-community-books - Check which community books are certified"
	@echo "  notebooks             - Generate Jupyter notebooks from .lisp files"
	@echo "  clean                 - Remove certification artifacts"
	@echo "  clean-notebooks       - Remove generated notebooks"
	@echo "  clean-all             - Remove all generated files"
	@echo "  test                  - Run Python tests"
	@echo "  install-deps          - Install Python dependencies"
	@echo "  install-rust          - Install Rust toolchain"
	@echo "  install-parinfer      - Install parinfer-rust CLI"
	@echo "  test-parinfer         - Test parinfer-rust installation"
	@echo "  cargo-run CMD=...     - Run a command with Cargo environment"
	@echo "  install-bridge-sbcl   - Install ACL2 Bridge SBCL port (PR #1882)"
	@echo "  check-bridge-sbcl     - Check if Bridge SBCL files are installed"
	@echo "  certify-bridge        - Certify ACL2 Bridge book"

