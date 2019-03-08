# Mini Statix

A playground implementation of the Statix constraint language in Haskell

This is meant to be a place to quickly prototype extensions and variations on the
core Statix language.

Currently we have:

- (A parser using 'happy')[./src/Statix/Syntax/Parser.y]
- (A monad supporting unification/binding/workqueue/data graphs)[./src/Statix/Solver/Monad.hs]
- (An interpreter for constraint programs)[./src/Statix/Solver.hs]
- (A minimal repl)[./src/Lib.hs]