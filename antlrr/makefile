
PYTHON_CHECK := $(shell command -v python3)
BREW_CHECK := $(shell command -v brew)
ANTLR_CHECK := $(shell command -v antlr4)

.PHONY: all brew python3 antlr4 TPTP_ANTLR_FILES

all: TPTP_ANTLR_FILES

brew:
ifeq ($(BREW_CHECK),)
	@echo "Homebrew not found. Installing Homebrew..."
	/bin/bash -c "$$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
else
	@echo "Homebrew already installed: $(BREW_CHECK)"
endif

python3: brew
ifeq ($(PYTHON_CHECK),)
	@echo "Python 3 not found. Installing Python 3 via Brew..."
	brew install python3
else
	@echo "Python 3 already installed: $(PYTHON_CHECK)"
endif

antlr4: python3
ifeq ($(ANTLR_CHECK),)
	@echo "ANTLR 4 tools not found. Installing via pip3..."
	pip3 install antlr4-tools
else
	@echo "ANTLR 4 tools already installed: $(ANTLR_CHECK)"
endif


TPTP_ANTLR_FILES: antlr4 TPTP.g4
	@echo "Generating TPTP ANTLR files..."
	antlr4 -Dlanguage=Python3 TPTP.g4 -visitor
