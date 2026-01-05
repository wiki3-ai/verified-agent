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

