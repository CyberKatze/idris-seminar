# Variables

# Targets
.PHONY: help build-doc

build-doc: ## Build latex docuemnt
	@nix build .#document
help: ## Displays this help message
	@echo "Usage: make [TARGET]"
	@echo ""
	@echo "Targets:"
	@awk 'BEGIN {FS = ":.*?## "}; /^[a-zA-Z_-]+:.*?## / { printf "  %-20s %s\n", $$1, $$2 }' $(MAKEFILE_LIST)
