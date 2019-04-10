all:
	stack build --verbosity=warn

run: exe
exe: all
	stack exec statix-exe

test:
	stack test

doc:
	stack haddock --keep-going --open

clean:
	stack clean

.PHONY: all exe test doc clean
.SILENT:
