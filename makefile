all:
	stack build

exe:
	stack exec statix-exe

test:
	stack test

.PHONY: test exe
