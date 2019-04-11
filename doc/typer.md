# Typing Ministatix

The static analysis for Ministatix consists of two clearly distinct stages:

- Naming
- Typing

## Naming

The namer disambiguates all variable names, replacing raw names with more informative ones:

1. Replace all raw variable occurences with paths (i.e. fancy de Bruijn indices).
2. Qualify all global name occurences (predicate names) with their module name.

For this we use a structure for manipulating lexical binding that we call `MonadLex`,
which we reuse for typing and runtime value lookups.
This pattern is an instantiation of the scopes-and-frames approach to binding,
but made specific for Ministatix.

## Typing

The typer checks various well-formedness properties of the named AST.
This includes, at this time:

- An arity check for predicate applications
- A sort analysis
- A permission analysis (see "Knowing When to Ask" draft)

The sort analysis and permission analysis are integrated mostly into a constraint collection pass
over the AST. The implementation is using the same unification machinery for sort unification as 
the solver uses for term unification.

Types are not recursive, so unification may seem overkill. However, the sort analysis computes
a fixedpoint over an entire module (all predicates in a module are mutually defined).
Doing the same analysis without unification would yield a much less declarative implementation.

### Implementation

The typechecker has access to a symboltable for all modules that are known and fully type checked.
Additionally it holds a pre-module-typing, which has a similar structure as the symbol table,
but holds a unifiable type structure (dag) instead of a ground type.

Unification is instantiated modulo a sub-typing lattice that is used to take least upper bounds
whenever we have an equation to solve.
This enables aggregation of node permissions during unification.
