STACK      ?= stack
SETUP_ARGS ?=
BUILD_ARGS ?=
EXEC_ARGS  ?=
TEST_ARGS  ?=
DOC_ARGS   ?= --keep-going --open
CLEAN_ARGS ?= --full
ARGS       ?= --verbosity=warn

all: build

setup:
	$(STACK) setup $(SETUP_ARGS) $(ARGS)

build: setup
	$(STACK) build $(BUILD_ARGS) $(ARGS)
	mkdir -p build
	ln -sfr ./.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/build/statix/statix build/statix

run: build
	$(STACK) exec statix-exe $(EXEC_ARGS) $(ARGS)

test: build
	$(STACK) test $(TEST_ARGS) $(ARGS)

doc:
	$(STACK) haddock $(DOC_ARGS) $(ARGS)

clean:
	$(STACK) clean $(CLEAN_ARGS) $(ARGS)
	-rm statix.cabal

.PHONY: all setup build run exe test doc clean
.SILENT:
