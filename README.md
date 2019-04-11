# Mini Statix

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

    make run

Other makefile targets are:
- `test` to run the test specification in `test/`;
- `clean` to remove the build artifacts;
- `doc` to build and show the generated documentation.


[1]: https://www.haskellstack.org/
