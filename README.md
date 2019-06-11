# Ministatix

A playground implementation of the Statix constraint language in Haskell.

This is meant to be a place to quickly prototype extensions and variations
on the core Statix language.

Currently we have:

- [A parser using 'happy'](./src/Statix/Syntax/Parser.y)
- [A monad supporting unification/binding/workqueue/data graphs](./src/Statix/Solver/Monad.hs)
- [An interpreter for constraint programs](./src/Statix/Solver.hs)
- [A minimal repl](./src/Lib.hs)


## Build and Run
To build this project, you need to have the [Haskell Toolstack][1]
(`brew install haskell-stack` on MacOS).  Build the project using:

    make

Enter the project's REPL using:

    ./statix repl

Check a file `input.aterm` against the specification `src/spec.mstx` using:

    ./statix check -I src spec input.aterm

The return code can be used to check the result of checking:
- `0` for satisfied constraints
- `64` for unsatisfied constraints
- `65` for stuckness of the solver
- `1` for other errors (spec doesn't parse, imported modules missing, etc)

Other makefile targets are:
- `setup` to setup the build environment;
- `build` to build the project;
- `test` to run the test specifications in `test/`;
- `clean` to remove the build artifacts;
- `doc` to build and show the generated documentation;
- `ghci` to open a Haskell Interactive propt in the project directory;
- `install` to install the built artifacts.


[1]: https://www.haskellstack.org/
