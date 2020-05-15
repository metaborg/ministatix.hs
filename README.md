# MiniStatix -- it is not a typo!

A playground implementation of the Statix constraint language in Haskell.

This is meant to be a place to quickly prototype extensions and variations
on the core Statix language.

It can execute a given ministatix specification on an aterm, or can be exercised
in a REPL.

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
- `clean` to remove the artifacts;
- `doc` to build and show the generated documentation;
- `ghci` to open a Haskell Interactive propt in the project directory;
- `install` to install the binary in your user's local bin.

## Editor support

There is barely any for this research language, but you can find an emacs syntax
highlighting definition in [tooling/](./tooling/).

[1]: https://www.haskellstack.org/
