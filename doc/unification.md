# Unification in Mini-Statix

Ministatix implements the "almost linear" unification algorithm described in Baader & Snyder[1].
This is a reformulation of Huet's algorithm based on the Union-Find datastructure.

The main "problem" of implementing unification is propagating equalities along chains of equations.
In Huet's algorithm this is addressed by using an indirect representation of terms as pointers into a graph.
As we unify (sub)terms, we discover equalities that we 'remember' by linking graph nodes into 
/equivalences classes/.
Classes have a single /representative/ that is tied to a /schema term/.
The schema term is always in functional form (i.e. not a unification variable), /unless/
the entire class consists of unification variables.

Concretely unification happens as follows;
given two terms `t₁ = f(x, g())` and `t₂ = f(y, y)` that we want to unify we:

1. Build a graph. We write `nodeid ↦ schema` for a representative node and `nodeid ↠ nodeid` for a
   node link (pointing to another node in the same class). By following links we should always
   end up in a representative.

		n₀ ↦ x
		n₁ ↦ y
		n₂ ↦ g()
		n₃ ↦ f(n₀, n₂)
		n₄ ↦ f(n₁, n₁)

2. Call `unify n₃ n₄`, which builds the so called unification closure.

   Since the schema of the tow nodes are both functional, we check that the constructors match.
   We take the union of the classes of `n₃` and `n₄`:

		n₀ ↠ n₁         -- link
		n₁ ↠ n₂         -- link
		n₂ ↦ g()
		n₃ ↦ n₄
		n₄ ↦ f(n₁, n₁)

   And recursively proceed on the pairs (`n₀, n₁`, `n₂, n₁`).
   Both `n₀` and `n₁` have variables as their schema.
   This means that we can trivially unify the pairs.
   This results in taking the union of the classes of the respective nodes:

		n₀ ↠ n₁         -- link
		n₁ ↠ n₂         -- link
		n₂ ↦ g()
		n₃ ↦ n₄
		n₄ ↦ f(n₁, n₁)

3. Now that we've built the closure we can check that the resulting graph is acyclic and if 
   that is the case the unification succeeded.
   We can build a term from it by recursively traversing the graph and instantiating nodes with
   schemas of representatives.
   For examples, building a term from `n₄` would find the representative of `n₁`, which is `n₂`, 
   and its schema `g()`, and build `f(g(), g())` from that.
   This is indeed the term we'd expect from unification of the input terms.
   
## Solver

In order to preserve the sharing that you get from unification, the whole solver
works on nodes in the unification closure graph that is part of the solver state.
We only convert terms back to trees as we exit the solver.

## Relation to full Statix

The Java implementation uses a similar strategy, but only builts nodes for variables in the
tree representation of the term.
It is unclear how the two algorithms compare other than that both seem to be correct.

[1] Frans Baader, Wayned Snyder, Unification Theory
