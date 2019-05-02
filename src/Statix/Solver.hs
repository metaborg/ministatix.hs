module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.HashMap.Strict as HM
import Data.HashSet as HS
import Data.Set as Set
import Data.Hashable
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Functor.Fixedpoint
import Data.List as List
import Data.Default
import Data.Sequence as Seq
import Data.Foldable as Fold
import qualified Data.Text as Text
import Data.Relation as Rel

import Control.Lens
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.Equiv
import Control.Monad.Unique

import Debug.Trace

import Statix.Regex as Re
import Statix.Syntax.Constraint as C
import Statix.Graph
import Statix.Graph.Paths
import Statix.Graph.Types as Graph
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical
import Statix.Solver.Types
import Statix.Solver.Reify
import Statix.Solver.Monad

import Unification as U hiding (TTm)

__trace__ = False

tracer :: String → a → a
tracer s a = if __trace__ then trace s a else a

tracerWithQueue :: SolverM s a → SolverM s a
tracerWithQueue c = do
  q   ← use queue
  let out = intercalate "\n" $ fmap format (Fold.toList q)
  tracer out c

  where
    format :: Goal s → String
    format (_, c, _) = show c

-- TODO make Reifiable a typeclass again
reifyPath :: SPath s (STmRef s) → SolverM s (STmRef s)
reifyPath (Graph.Via (n, l, t) p) = do
  n  ← construct (Tm (SNodeF n))
  l  ← construct (Tm (SLabelF l t))
  pr ← reifyPath p
  construct (Tm (SPathConsF n l pr))
reifyPath (Graph.End n) = do
  n ← construct (Tm (SNodeF n))
  construct (Tm (SPathEndF n))

panic :: String → SolverM s a
panic s = throwError (Panic s)

pushGoal :: SGen → Constraint₁ → SolverM s ()
pushGoal i c = do
  env ← ask
  queue %= (\q → q Seq.|> (env, c, i))

-- | Delay a constraint by pushing it back on the work queue.
-- The constraint gets tagged by the current solver generation,
-- marking the fact that we have tried solving it in this generation,
-- but could not.
delay :: Constraint₁ → SolverM s ()
delay c = do
  gen ← use generation
  pushGoal gen c

newGoal :: Constraint₁ → SolverM s ()
newGoal c = do
  pushGoal minBound c
  next -- fresh meat

-- | Pop a constraint from the work queue if it is non-empty,
-- and if the constraint was put in the queue before the current solver
-- generation.
-- 
-- If the queue contains only goals that were created in the current
-- generation of the solver, the solver has made no progress and
-- cannot make progress: the solver is stuck.
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  q   ← use queue
  gen ← use generation

  -- If we pop a goal and we find that its generation is
  -- at or after the solver's current generation,
  -- then the solver has made no progress and we are stuck.
  -- As the generation is monotonically increasing for goals
  -- pushed to the end of the queue, we know the queue contains
  -- no more goals from an earlier generation.
  case Seq.viewl $ q of
    Seq.EmptyL           → return Nothing
    c@(_, _, lasttry) Seq.:< cs
      | lasttry >= gen → do
          throwError StuckError
      | otherwise          → do
          queue %= const cs
          return (Just c)

-- | Continue with the next goal.
-- As we are making progress, we increment
-- the solver's generation counter by one.
next :: SolverM s ()
next = do
  st <- get
  generation %= (+1)
  return ()

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [Ident] → SolverM s a → SolverM s a
openExist ns c = do
  bs ← mapM mkBinder ns
  enters bs c

  where
    mkBinder name = do
      v ← freshVar name
      return (name, v)

checkTerm ces n ls = do
  t ← getSchema n
  return $ case t of
    (SNode n) →
      case ces Map.!? n of
        Nothing  → Set.empty
        Just re  →
          let critics = (\l →
                           if not $ Re.empty $ match l re
                           then Set.singleton (n, l)
                           else Set.empty) <$> (Set.toList ls)
          in Set.unions critics
    _ → Set.empty

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → SolverM s (Set (SNode s, Label))
checkCritical ces (CAnd l r) = do
  lc ← checkCritical ces l
  rc ← checkCritical ces r
  return (lc `Set.union` rc)
checkCritical ces (CEx xs c) = do
  openExist xs $ checkCritical ces c
checkCritical ces (CEdge x e y)
  | (Label l _) ← e = do
      t₁ ← resolve x
      checkTerm ces t₁ (Set.singleton l)
  | otherwise = throwError TypeError
checkCritical ces (CApply qn ts) = do
  ts ← mapM toDag ts
  -- get type information for p
  formals  ← view (symbols . to (!!! qn) . to sig)
  critters ← zipWithM (\t (_,ty) → checkParam t ty) ts formals
  return $ Set.unions critters
  where
    checkParam t ty
      | TNode (In ls)    ← ty = checkTerm ces t ls
      | TNode (InOut ls) ← ty = checkTerm ces t ls
      | otherwise             = return Set.empty
checkCritical _ _ = return Set.empty

queryGuard :: Map (SNode s) (Regex Label) → SolverM s (Set (SNode s, Label))
queryGuard ce = do
  cs ← use queue
  Set.unions <$> mapM (\(e, c, _) → local (const e) $ checkCritical ce c) cs

-- | Embedding of syntactical terms into the DAG representation of terms
toDag :: Term₁ → SolverM s (STmRef s)
toDag (C.Var p)    =
  resolve p
toDag (TTm t) = do
  id ← fresh
  t ← mapM toDag t
  newClass (Rep (STm t) id)
toDag (Label l t) = do
  id ← fresh
  t ← mapM toDag t
  newClass (Rep (SLabel l t) id)
toDag (PathCons x l t₂) = do
  id ← fresh
  n  ← resolve x
  t₂ ← toDag t₂
  l  ← toDag l
  newClass (Rep (SPathCons n l t₂) id)
toDag (PathEnd x) = do
  id ← fresh
  n ← resolve x
  newClass (Rep (SPathEnd n) id)

toDag _ = throwError (Panic "Not implemented")

matches :: STmRef s → Matcher Term₁ → SolverM s a → SolverM s a
matches t (Matcher ns g eqs) ma = 
  tracer ("branch: " ++ show g) $ openExist ns $ do
    g ← toDag g
    g `subsumes` t -- check if we have a match, will throw otherwise

    -- check the equalities
    forM eqs $ \(lhs, rhs) → do
      lhs ← toDag lhs
      rhs ← toDag rhs
      lhs `equiv` rhs

    ma

-- | Try to solve a focused constraint.
-- This should not be a recursive function, as not to infer with scheduling.
solveFocus :: Constraint₁ → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (Unsatisfiable "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← toDag t1
  t2' ← toDag t2
  unify t1' t2'
  next

solveFocus (CAnd l r) = do
  newGoal l
  newGoal r

solveFocus (CEx ns c) =
  openExist ns (newGoal c)

solveFocus (CNew x) = do
  t  ← resolve x
  u  ← newNode Nothing
  t' ← construct (Tm (SNodeF u))
  catchError
    (unify t t')
    (\ err → throwError (Unsatisfiable "Not fresh!"))
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

solveFocus (CQuery x r y) = do
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
      unify pref t
      next
    (SAns []) →
      throwError (Unsatisfiable $ show c ++ " (No paths)")
    (SAns ps) →
      throwError (Unsatisfiable $ show c ++ " (More than one path: ") -- TODO  ++ show ps ++ ")")
    t →
      throwError TypeError

solveFocus (CData x t) = do
  x ← resolve x >>= getSchema

  -- check if sufficiently ground
  case x of
    (SNode n) → do
      t' ← getDatum n
      t  ← toDag t

      -- check if a datum is already associated
      -- with the node
      case t' of
        Nothing →
          setDatum n t
        Just t' → do
          unify t t'
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
   (Pred _ σ c) ← getPredicate p
   -- normalize the parameters
   ts' ← mapM toDag ts

   -- bind the parameters
   enters (List.zip (fmap fst σ) ts') $ do
     -- solve the body
     tracer ("unfold " ++ show p ++ " with " ++ show ts) $ newGoal c

solveFocus (CMatch t bs) = do
  t' ← tracer ("matching " ++ show t) $ toDag t
  σ  ← getSchema t'
  case σ of
    (U.Var x) → throwError StuckError
    (U.Tm f)  → solveBranch t' bs

  where
    solveBranch :: STmRef s → [Branch₁] → SolverM s ()
    solveBranch t' []                    = do
      t' ← toTree t'
      throwError $ Unsatisfiable $ "No match for '" ++ show t' ++ "'"
    solveBranch t' ((Branch match c):br) = do
      -- determine if the matcher matches the term
      -- and schedule the body of the branch in that environment
      catchError (matches t' match (newGoal c))
        (\case
          Unsatisfiable s → solveBranch t' br
          e               → throwError e
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

      case t of
        Nothing  → return False -- TODO issue #17
        (Just t) → catchError
          (matches t m (return True))
          (\case
            Unsatisfiable s → return False
            e               → throwError e
          )

type Unifier s = HashMap Ident (STree s)

-- | A simple means to getting a unifier out of ST, convert everything to a string
unifier :: SolverM s (Unifier s)
unifier = do
  env ← view locals
  mapM toTree (head env)

formatUnifier :: Unifier s → String
formatUnifier fr =
  let bs = fmap formatBinding (HM.toList fr)
  in intercalate "\n" bs
  where
    formatBinding (k , t) = "  " ++ Text.unpack k ++ " ↦ " ++ (show t)

-- | Constraint scheduler
-- | The solver loop just continuously checks the work queue,
-- steals an item and focuses it down, until nothing remains.
-- When the work is done it grounds the solution and returns it.
schedule :: SolverM s String
schedule = do
  st ← get
  c  ← popGoal
  case c of
    Just (env, c, _) → do
      local (const env) $ do
        catchError (solveFocus c)
          (\case
            -- reschedule stuck goals
            StuckError      → local (const env) (delay c)
            Unsatisfiable s → throwError $ Unsatisfiable $ "constraint " ++ show c ++ " failed with: " ++ s
            e          → throwError e
          )
      schedule

    -- done, gather up the solution (graph and top-level unifier)
    Nothing → do
      φ     ← unifier
      return $ formatUnifier φ

-- | Construct a solver for a raw constraint
kick :: SymbolTable → Constraint₁ → (forall s. SolverM s String)
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → set symbols sym def) $ do
    case c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
        newGoal b
        schedule

      c → do
        newGoal c
        schedule

-- | Construct and run a solver for a constraint
solve :: SymbolTable → Constraint₁ → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymbolTable → Constraint₁ → Bool
check p c = let (ei, _) = solve p c in isRight ei
