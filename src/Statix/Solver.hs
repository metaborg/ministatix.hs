module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.List as List
import Data.Default
import Data.Relation as Rel
import Data.HashMap.Strict as HM

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

solveFocus CTrue  = return ()
solveFocus CFalse = unsatisfiable "Say hello to Falso"

solveFocus (CEq t1 t2) = do
  t1' ← toDag t1
  t2' ← toDag t2
  escalateUnificationError $ unify t1' t2'
  next

solveFocus (CNotEq t1 t2) = do
  escalateUnificationError $ passesGuard (GNotEq t1 t2)
  next

solveFocus (CAnd l r) = do
  newGoal l
  newGoal r

solveFocus (CEx ns c) =
  openExist ns (newGoal c)

solveFocus (CNew x d) = do
  t  ← resolve x
  d  ← toDag d
  u  ← newNode d
  t' ← construct (Tm (SNodeF u))
  catchError
    (unify t t')
    (\ err → unsatisfiable "Cannot get ownership of existing node")
  next

solveFocus (CEdge x (Label l t) y) = do
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

solveFocus c@(CQuery x r y) = do
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

solveFocus c@(COne x t) = do
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

solveFocus c@(CNonEmpty x) = do
  ans ← resolve x >>= getSchema
  case ans of
    (U.Var x)      → throwError StuckError
    (SAns [])      → unsatisfiable "No paths in answer set"
    (SAns (p : _)) → next
    t              → throwError TypeError

solveFocus (CData x t) = do
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

solveFocus (CEvery x (Branch m c)) = do
  ans ← resolve x >>= getSchema
  case ans of
    -- not ground enough
    (U.Var x) → throwError StuckError
    -- expand to big conjunction conjunction
    (SAns ps) → do
      forM ps $ \p → do
        -- bind the path
        pn ← reifyPath p
        matches pn m (newGoal c)
      next
    t →
      throwError TypeError

solveFocus (CApply p ts) = do
   (Pred _ σ c) ← view (symbols.getPred p)
   -- normalize the parameters
   ts' ← mapM toDag ts

   -- bind the parameters
   enters (FrPred p) (List.zip (fmap fst σ) ts') $ do
     -- solve the body
     tracer ("unfold " ++ show p ++ " with " ++ show ts) $ newGoal c

solveFocus (CMatch t bs) = do
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

solveFocus (CMin x lt z) = do
  σ ← resolve x >>= getSchema
  case σ of
    (U.Var x)  → throwError StuckError
    (SAns ans) → do
      let min = setLeMin (comp lt) ans
      ansRef  ← construct (Tm (SAnsF min))
      b       ← resolve z
      unify b ansRef
      next
    _          → throwError TypeError
  where
    comp :: PathComp → Rel (SPath s t) (SPath s t)
    comp (Lex lt) p q =
      reflexiveClosure
        (pathLT (transitiveClosure (finite lt)))
        (labels p)
        (labels q)

solveFocus (CFilter x m z) = do
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
kick :: SymbolTable₂ → Constraint₁ → SolverM s (Unifier s)
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → set symbols sym def) $ do
    case c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
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
  | IsStuck [String]

-- | Construct and run a solver for a constraint and
-- extract an ST free solution
solve :: SymbolTable₂ → Constraint₁ → ST s (Result s)
solve symtab c = do
  solution ← runSolver' $ do
    catchError
      (do unifier ← kick symtab c 
          graph   ← dumpgraph
          return (IsSatisfied unifier graph))
      (\case 
          StuckError → do
            q ← formatQueue
            return $ IsStuck q
          e → do
            graph ← dumpgraph
            return (IsUnsatisfiable e graph))

  -- TODO improve once we factor SolverM into an interface...
  return $ either undefined (\r → r) $ fst $ solution

-- | Check satisfiability of a program
check :: SymbolTable₂ → Constraint₁ → Bool
check p c = runST $ do
                  sol ← solve p c
                  case sol of
                    (IsSatisfied _ _) → return True
                    otherwise         → return False
