STACK        ?= stack
SETUP_ARGS   ?=
BUILD_ARGS   ?=
RUN_ARGS     ?=
TEST_ARGS    ?=
DOC_ARGS     ?= --keep-going --open
CLEAN_ARGS   ?= --full
GHCI_ARGS    ?=
INSTALL_ARGS ?=
ARGS         ?=
STACK_ARGS   ?= --verbosity=warn

all: build

setup:
	$(STACK) setup $(SETUP_ARGS) $(STACK_ARGS)

build: setup
	$(STACK) build $(BUILD_ARGS) $(STACK_ARGS)

run: build
	$(STACK) exec $(RUN_ARGS) $(STACK_ARGS) -- statix $(ARGS)

test: build
	$(STACK) test $(TEST_ARGS) $(STACK_ARGS)

doc:
	$(STACK) haddock $(DOC_ARGS) $(STACK_ARGS)

clean:
	$(STACK) clean $(CLEAN_ARGS) $(STACK_ARGS)
	-rm statix.cabal

ghci:
	$(STACK) ghci $(GHCI_ARGS) $(STACK_ARGS)

install:
	$(STACK) install $(INSTALL_ARGS) $(STACK_ARGS)

.PHONY: all setup build run test doc clean ghci install
.SILENT:
