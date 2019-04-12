STACK       ?= stack
SETUP_FLAGS ?=
BUILD_FLAGS ?=
EXEC_FLAGS  ?=
TEST_FLAGS  ?=
DOC_FLAGS   ?= --keep-going --open
CLEAN_FLAGS ?= --full
FLAGS       ?= --verbosity=warn

all: build

setup:
	$(STACK) setup $(SETUP_FLAGS) $(FLAGS)

build: setup
	$(STACK) build $(BUILD_FLAGS) $(FLAGS)

run: build
	$(STACK) exec statix-exe $(EXEC_FLAGS) $(FLAGS)

test: build
	$(STACK) test $(TEST_FLAGS) $(FLAGS)

doc:
	$(STACK) haddock $(DOC_FLAGS) $(FLAGS)

clean:
	$(STACK) clean $(CLEAN_FLAGS) $(FLAGS)
	-rm statix.cabal

.PHONY: all setup build run exe test doc clean
.SILENT:
