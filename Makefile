# Makefile for ACL2 Verified Agent

.PHONY: all clean cert test

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

# Clean all generated files
clean:
	rm -f src/*.cert src/*.cert.out src/*.lx64fsl src/*.fasl src/*.port
	rm -f src/*.pcert0 src/*.pcert1 src/*.acl2x

# Run Python tests for acl2-mcp
test:
	cd acl2-mcp && python -m pytest -v

# Install Python dependencies
install-deps:
	pip install -e acl2-mcp

# Help
help:
	@echo "Available targets:"
	@echo "  all        - Certify main ACL2 books (default)"
	@echo "  cert       - Certify verified-agent.lisp"
	@echo "  cert-all   - Certify all books including runtime"
	@echo "  clean      - Remove all generated files"
	@echo "  test       - Run Python tests"
	@echo "  install-deps - Install Python dependencies"
