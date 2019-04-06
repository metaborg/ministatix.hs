all:
	stack build

exe: all
	stack exec statix-exe

test:
	stack test

.PHONY: test exe
