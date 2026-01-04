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
all: cert

# Certify ACL2 books
cert:
	cd src && cert.pl verified-agent.lisp

# Full certification including runtime
cert-all:
	cd src && cert.pl verified-agent.lisp
	cd src && cert.pl agent-runner.lisp
	cd src && cert.pl chat-demo.lisp

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

# Run Python tests for acl2-mcp
test:
	cd acl2-mcp && python -m pytest -v

# Install Python dependencies
install-deps:
	pip install -e acl2-mcp

# Help
help:
	@echo "Available targets:"
	@echo "  all           - Certify main ACL2 books (default)"
	@echo "  cert          - Certify verified-agent.lisp"
	@echo "  cert-all      - Certify all books including runtime"
	@echo "  notebooks     - Generate Jupyter notebooks from .lisp files"
	@echo "  clean         - Remove certification artifacts"
	@echo "  clean-notebooks - Remove generated notebooks"
	@echo "  clean-all     - Remove all generated files"
	@echo "  test          - Run Python tests"
	@echo "  install-deps  - Install Python dependencies"

