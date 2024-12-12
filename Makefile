# Variables
DOC_DIR = report 
# Frontend commands
PNPM_RUN_BUILD = pnpm run build
PNPM_INSTALL = pnpm install
PNPM_DEV = pnpm run dev
PNPM_TEST = pnpm playwright test 


# Targets
.PHONY: help

all: pre-front pre-back ## Prepares both frontend and backend

build-doc: $(DOC_DIR)/main.tex ## Build latex docuemnt

