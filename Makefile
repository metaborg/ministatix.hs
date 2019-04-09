all:
	stack build

run: exe
exe:
	stack build --verbosity=warn
	stack exec statix-exe

test:
	stack test

clean:
	stack clean

.PHONY: all exe test clean
.SILENT:
