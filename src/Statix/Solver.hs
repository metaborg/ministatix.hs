module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.HashMap.Strict as HM
import Data.HashSet as HS
import Data.Set as Set
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Functor.Fixedpoint
import Data.List as List
import Data.Default
import Data.Sequence
import qualified Data.Text as Text
import qualified Data.Sequence as Seq

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

import Unification as U

-- TODO make Reifiable a typeclass again
reifyPath :: SPath s → SolverM s (STmRef s)
reifyPath (Graph.Via (n, l) p) = do
  n  ← construct (Tm (SNodeF n))
  pr ← reifyPath p
  construct (Tm (SPathF n l pr))
reifyPath (Graph.End n) =
  construct (Tm (SNodeF n))

panic :: String → SolverM s a
panic s = throwError (Panic s)

-- | Push a constraint as a goal on the work queue.
-- The goal's generation is the solver's generation when it was
-- pushed on the queue.
pushGoal :: Constraint₁ → SolverM s ()
pushGoal c = do
  st  ← get
  env ← ask
  put st { queue = queue st Seq.|> (env, c, generation st)}

-- | Pop a constraint from the work queue if it is non-empty,
-- and if the constraint was put in the queue before the current solver
-- generation.
-- 
-- If the queue contains only goals that were created in the current
-- generation of the solver, the solver has made no progress and
-- cannot make progress: the solver is stuck.
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  st ← get
  -- We pop only those goals whose generation is before
  -- the solver's current generation. If there are none, but the
  -- queue is not empty, we are apparently stuck.
  let xs = Seq.filter (\(_, _, gen) -> gen < generation st) (queue st)
  case Seq.viewl xs of
    Seq.EmptyL    → if Seq.null $ queue st
      then return Nothing
      else throwError StuckError
    (c Seq.:< cs) → do
      liftState $ put (st { queue = cs })
      return (Just c)

-- | Continue with the next goal.
-- As we are making progress, we increment
-- the solver's generation counter by one.
next :: SolverM s ()
next = do
  st <- get
  put st { generation = generation st + 1 }
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

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → SolverM s (Set (SNode s, Label))
checkCritical ces = cataM check
  where
    check (CAndF l r) = return (l `Set.union` r)
    check (CExF xs c) = return c
    check (CEdgeF x l y) = do
      t₁ ← resolve x >>= getSchema
      case t₁ of
        (SNode n) → 
          case ces Map.!? n of
            Nothing  → return Set.empty
            Just re  →
              if not $ Re.empty $ match l re
              then return $ Set.singleton (n, l)
              else return Set.empty
        _ → return Set.empty
    check (CApplyF p ts) = return Set.empty -- TODO!
    check _ = return Set.empty

queryGuard :: Map (SNode s) (Regex Label) → SolverM s (Set (SNode s, Label))
queryGuard ce = do
  cs ← liftState $ gets queue
  Set.unions <$> mapM (\(e, c, _) → local (const e) $ checkCritical ce c) cs

-- | Embedding of syntactical terms into the DAG representation of terms
toDag :: Term₁ → SolverM s (STmRef s)
toDag (C.Var p)    =
  resolve p
toDag (Con c ts) = do
  id  ← fresh
  ts' ← mapM toDag ts
  newClass (Rep (SCon c ts') id)
toDag (Label l) = do
  id ← fresh
  newClass (Rep (SLabel l) id)
toDag (Path t₁ l t₂) = do
  id ← fresh
  t₁ ← toDag t₁
  t₂ ← toDag t₂
  newClass (Rep (SPath t₁ l t₂) id)
toDag _ = throwError (Panic "Not implemented")

-- | Try to solve a focused constraint
solveFocus :: Constraint₁ → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (Unsatisfiable "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← toDag t1
  t2' ← toDag t2
  unify t1' t2'
  next

solveFocus (CAnd l r) = do
  pushGoal r
  solveFocus l

solveFocus (CEx ns c) =
  openExist ns (solveFocus c)

solveFocus (CNew x) = do
  t  ← resolve x
  u  ← newNode Nothing
  t' ← construct (Tm (SNodeF u))
  catchError
    (unify t t')
    (\ err → throwError (Unsatisfiable "Not fresh!"))
  next

solveFocus c@(CEdge x l y) = do
  t₁ ← resolve x >>= getSchema
  t₂ ← resolve y >>= getSchema
  case (t₁ , t₂) of
    (SNode n, SNode m) → do
      newEdge (n, l, m)
      next
    (U.Var _, _)       → pushGoal c
    (_ , U.Var _)      → pushGoal c
    _                  → throwError TypeError

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
        pushGoal (trace "Delaying query" c)
        next

    (U.Var _) → pushGoal c
    _         → throwError TypeError

solveFocus c@(COne x t) = do
  t   ← toDag t
  ans ← resolve x >>= getSchema
  case ans of
    (U.Var x) →
      pushGoal c
    (SAns (p : [])) → do
      pref ← reifyPath p
      unify pref t
      return ()
    (SAns []) →
      throwError (Unsatisfiable $ show c ++ " (No paths)")
    (SAns ps) →
      throwError (Unsatisfiable $ show c ++ " (More than one path: " ++ show ps ++ ")")
    t →
      throwError TypeError

solveFocus c@(CEvery x y c') = do
  ans ← resolve y >>= getSchema
  case ans of
    -- not ground enough
    (U.Var x) →
      pushGoal c
    -- expand to big conjunction conjunction
    (SAns ps) → do
      mapM_ (\p → do
                -- bind the path
                pn ← reifyPath p
                enters [(x , pn)] 
                  -- push the goal in the extended scope
                  (pushGoal c')
            ) ps
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
     solveFocus c

solveFocus _ = throwError (Panic "Not implemented")

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

-- | Construct a solver for a raw constraint
kick :: SymbolTable → Constraint₁ → (forall s. SolverM s (String, IntGraph Label ()))
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → set symbols sym def) $ do
    case c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
        pushGoal b
        next
        loop

      c → do
        pushGoal c
        next
        loop

  where
  -- | The solver loop just continuously checks the work queue,
  -- steals an item and focuses it down, until nothing remains.
  -- When the work is done it grounds the solution and returns it.
  loop :: SolverM s (String, IntGraph Label ())
  loop = do
    st ← get
    c  ← popGoal
    case c of
      Just (env, c, _) → do
        local (const env) (solveFocus c)
        loop
      Nothing → do
        -- done, gather up the solution (graph and top-level unifier)
        s ← get
        g ← liftST $ (toIntGraph (graph s))
        φ ← unifier
        return (show φ, void g)

-- | Construct and run a solver for a constraint
solve :: SymbolTable → Constraint₁ → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymbolTable → Constraint₁ → Bool
check p c = isRight $ solve p c
