module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.List as List
import Data.Default
import Data.Relation as Rel
import Data.HashMap.Strict as HM
import Data.Maybe (listToMaybe)

import Control.Lens
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Statix.Syntax as Syn
import Statix.Graph
import Statix.Graph.Paths
import Statix.Graph.Types as Graph
import Statix.Analysis.Lexical

import Statix.Solver.Types
import Statix.Solver.Monad
import Statix.Solver.Terms
import Statix.Solver.Guard
import Statix.Solver.Errors
import Statix.Solver.Scheduler
import Statix.Solver.Debug
import Statix.Solver.Scala

import Unification as U hiding (TTm)

reifyPath :: SPath s (STmRef s) → SolverM s (STmRef s)
reifyPath (Graph.Via (n, l, t) p) = do
  n  ← construct (Tm (SNodeF n))
  l  ← construct (Tm (SLabelF l t))
  pr ← reifyPath p
  construct (Tm (SPathConsF n l pr))
reifyPath (Graph.End n) = do
  n ← construct (Tm (SNodeF n))
  construct (Tm (SPathEndF n))

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [Ident] → SolverM s a → SolverM s a
openExist ns c = do
  bs ← mapM mkBinder ns
  enters FrExist bs c

  where
    mkBinder name = do
      v ← freshVar name
      return (name, v)

passesGuard :: Guard Term₁ → SolverM s ()
passesGuard (GEq lhs rhs) = do
  lhs ← toDag lhs
  rhs ← toDag rhs
  void $ lhs `equiv` rhs
passesGuard (GNotEq lhs rhs) = do
  lhs ← toDag lhs
  rhs ← toDag rhs

  -- invert equiv
  neq ← notequiv lhs rhs
  if neq
    then next
    else throwError $ UnificationError "Terms are not not equal"

matches :: STmRef s → Matcher Term₁ → SolverM s a → SolverM s a
matches t (Matcher ns g eqs) ma = 
  tracer ("branch: " ++ show g) $ openExist ns $ do
    g ← toDag g
    g `subsumes` t -- check if we have a match, will throw otherwise

    -- check the equalities
    forM eqs passesGuard
    ma

-- | Try to solve a focused constraint.
-- This should not be a recursive function, as not to infer with scheduling.
solveFocus :: Constraint₁ → SolverM s ()

solveFocus (CTrue _)  = return ()
solveFocus (CFalse _) = unsatisfiable "Say hello to Falso"

solveFocus (CEq _ t1 t2) = do
  t1' ← toDag t1
  t2' ← toDag t2
  escalateUnificationError $ unify t1' t2'
  next

solveFocus (CNotEq _ t1 t2) = do
  escalateUnificationError $ passesGuard (GNotEq t1 t2)
  next

solveFocus (CAnd _ l r) = do
  newGoal l
  newGoal r

solveFocus (CEx _ ns c) =
  openExist ns (newGoal c)

solveFocus (CNew _ x d) = do
  t  ← resolve x
  d  ← toDag d
  u  ← newNode d
  t' ← construct (Tm (SNodeF u))
  catchError
    (unify t t')
    (\ err → unsatisfiable "Cannot get ownership of existing node")
  next

solveFocus (CEdge _ x (Label l t) y) = do
  t₁ ← resolve x >>= getSchema
  t₂ ← resolve y >>= getSchema
  case (t₁ , t₂) of
    (SNode n, SNode m) → do
      t ← mapM toDag t
      newEdge (n, l, t, m)
      next
    (U.Var _, _)  → throwError StuckError
    (_ , U.Var _) → throwError StuckError
    _             → throwError TypeError

solveFocus c@(CQuery _ x r y) = do
  t ← resolve x >>= getSchema
  case t of
    -- If the source node is ground
    -- then we can attempt to solve the query
    (SNode n)  → do
      -- first we check the guard
      es ← findReachable n r
      stuckOn ← queryGuard es

      if List.null stuckOn then do
        -- if it passes we solve the query
        ans    ← runQuery n r
        ansRef ← construct (Tm (SAnsF ans))
        b      ← resolve y
        unify b ansRef
        next
      else do
        throwError StuckError

    (U.Var _) → throwError StuckError
    _         → throwError TypeError

solveFocus c@(COne _ x t) = do
  t   ← toDag t
  ans ← resolve x >>= getSchema
  case ans of
    (U.Var x) →
      throwError StuckError
    (SAns (p : [])) → do
      pref ← reifyPath p
      escalateUnificationError $ unify pref t
      next
    (SAns []) →
      unsatisfiable "No paths in answer set"
    (SAns ps) →
      unsatisfiable "More than one path in answer set"
    t →
      throwError TypeError

solveFocus c@(CNonEmpty _ x) = do
  ans ← resolve x >>= getSchema
  case ans of
    (U.Var x)      → throwError StuckError
    (SAns [])      → unsatisfiable "No paths in answer set"
    (SAns (p : _)) → next
    t              → throwError TypeError

solveFocus (CData _ x t) = do
  x ← resolve x >>= getSchema

  -- check if sufficiently ground
  case x of
    (SNode n) → do
      t' ← getDatum n
      t  ← toDag t

      -- check if a datum is already associated
      -- with the node
      escalateUnificationError $ unify t t'
      next
    (U.Var x) → throwError StuckError
    _         → throwError TypeError

solveFocus (CEvery _ x (Branch m c)) = do
  ans ← resolve x >>= getSchema
  case ans of
    -- not ground enough
    (U.Var x) → throwError StuckError
    -- expand to big conjunction
    (SAns ps) → do
      forM ps $ \p → do
        -- bind the path
        pn ← reifyPath p
        matches pn m (newGoal c)
      next
    t →
      throwError TypeError

solveFocus (CApply _ p ts) = do
   (Pred _ _ σ c) ← view (symbols.getPred p)
   -- normalize the parameters
   ts' ← mapM toDag ts

   -- bind the parameters
   enters (FrPred p) (List.zip (fmap (^._1) σ) ts') $ do
     -- solve the body
     tracer ("unfold " ++ show p ++ " with " ++ show ts) $ newGoal c

solveFocus (CMatch _ t bs) = do
  t' ← tracer ("matching " ++ show t) $ toDag t
  solveBranch t' bs

  where
    solveBranch :: STmRef s → [Branch₁] → SolverM s ()
    solveBranch t' []                    = do
      t' ← toTree t'
      unsatisfiable $ "No match for '" ++ show t' ++ "'"
    solveBranch t' ((Branch match c):br) = do
      -- determine if the matcher matches the term
      -- and schedule the body of the branch in that environment
      catchError (matches t' match (newGoal c))
        (\case
          UnificationError _ → solveBranch t' br
          e                  → throwError e
        )

solveFocus (CMin _ x lt z) = do
  σ ← resolve x >>= getSchema
  case σ of
    (U.Var x)  → throwError StuckError
    (SAns ans) → do
      let min = setMin lt ans
      ansRef  ← construct (Tm (SAnsF min))
      b       ← resolve z
      unify b ansRef
      next
    _          → throwError TypeError
  where
    lexico lt p q =
      reflexiveClosure
        (pathLT (transitiveClosure (finite lt))) p q

    setMin (RevLex lt) ans = setLeMin (\ p q → lexico lt (reverse $ labels p) (reverse $ labels q)) ans
    setMin (Lex lt) ans = setLeMin (\ p q → lexico lt (labels p) (labels q)) ans
    setMin ScalaOrd ans = setLtMin (\ p q → scala (labels p) (labels q)) ans

solveFocus (CFilter _ x m z) = do
  σ ← resolve x >>= getSchema
  case σ of
    (U.Var x)  → throwError StuckError
    (SAns ans) → do
      ans'   ← filterM (filt m) ans
      ansRef ← construct (Tm (SAnsF ans'))
      b      ← resolve z
      unify b ansRef
      next
    _          → throwError TypeError
  where
    filt :: PathFilter Term₁ → SPath s t → SolverM s Bool
    filt (MatchDatum m) p = do
      let tgt = target p
      t ← getDatum tgt

      catchError
        (matches t m (return True))
        (\case
          UnificationError _ → return False
          e                  → throwError e
        )

-- | Construct a solver for a raw constraint
kick :: SymbolTable₃ → Constraint₁ → SolverM s (Unifier s)
kick sym c =
  local (\_ → set symbols sym def) $ do
    case c of
      -- open the top level exists if it exists
      (CEx _ ns b) → openExist ns $ do
        newGoal b
        schedule solveFocus
        unifier

      c → do
        newGoal c
        schedule solveFocus
        return HM.empty

data Result s
  = IsSatisfied (Unifier s) (IntGraph Label String)
  | IsUnsatisfiable StatixError (IntGraph Label String)
  | IsStuck [String] (IntGraph Label String)

-- | Construct and run a solver for a constraint and
-- extract an ST free solution
solve :: SymbolTable₃ → Constraint₁ → ST s (Result s)
solve symtab c = do
  solution ← runSolver' $ do
    catchError
      (do unifier ← kick symtab c 
          graph   ← dumpgraph
          return (IsSatisfied unifier graph))
      (\case 
          StuckError → do
            q ← formatQueue
            graph ← dumpgraph
            return $ IsStuck q graph
          e → do
            graph ← dumpgraph
            return (IsUnsatisfiable e graph))

  -- TODO improve once we factor SolverM into an interface...
  return $ either undefined (\r → r) $ fst $ solution

-- | Check satisfiability of a program
check :: SymbolTable₃ → Constraint₁ → Bool
check p c = runST $ do
                  sol ← solve p c
                  case sol of
                    (IsSatisfied _ _) → return True
                    otherwise         → return False
