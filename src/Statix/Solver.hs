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
newGoal = pushGoal minBound

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

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → SolverM s (Set (SNode s, Label))
checkCritical ces = cataM check
  where
    checkTerm n ls = do
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

    checkParam t ty
      | TNode (In ls)    ← ty = checkTerm t ls
      | TNode (InOut ls) ← ty = checkTerm t ls
      | otherwise             = return Set.empty

    check (CAndF l r) = return (l `Set.union` r)
    check (CExF xs c) = return c
    check (CEdgeF x l y) = do
      t₁ ← resolve x
      checkTerm t₁ (Set.singleton l)
    check (CApplyF qn ts) = do
      ts ← mapM toDag ts
      -- get type information for p
      formals  ← view (symbols . to (!!! qn) . to sig)
      critters ← zipWithM (\t (_,ty) → checkParam t ty) ts formals
      return $ Set.unions critters
    check _ = return Set.empty

queryGuard :: Map (SNode s) (Regex Label) → SolverM s (Set (SNode s, Label))
queryGuard ce = do
  cs ← use queue
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
  newGoal r
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
    (U.Var _, _)  → delay c
    (_ , U.Var _) → delay c
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
        trace "Delaying" $  delay c

    (U.Var _) → delay c
    _         → throwError TypeError

solveFocus c@(COne x t) = do
  t   ← toDag t
  ans ← resolve x >>= getSchema
  case ans of
    (U.Var x) →
      delay c
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

solveFocus c@(CData x t) = do
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
    (U.Var x) → delay c
    _         → throwError TypeError

solveFocus c@(CEvery x y c') = do
  ans ← resolve y >>= getSchema
  case ans of
    -- not ground enough
    (U.Var x) →
      delay c
    -- expand to big conjunction conjunction
    (SAns ps) → do
      forM ps $ \p → do
        -- bind the path
        pn ← reifyPath p
        -- push the goal in the extended scope
        enters [(x , pn)] 
          (newGoal c')
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

solveFocus c@(CMatch t bs) = do
  t ← toDag t
  σ ← getSchema t
  case σ of
    (U.Var x) → delay c
    (U.Tm f)  → solveBranch t bs

  where
    solveBranch :: STmRef s → [Branch₁] → SolverM s ()
    solveBranch t [] = throwError $ Unsatisfiable "No match"
    solveBranch t ((Branch ns g c):br) = do
      thisOne ← openExist ns $ do
        g ← toDag g
        thisOne ← catchError
          (do -- try this branch
            tcopy ← freshen t
            g `subsumes` tcopy

            -- no need to try other branches
            return True
          )
          (\_ → return False)

        -- only now we commit the binding
        if thisOne
          then do
            g `unify` t
            solveFocus c
            return True
          else
            return False

      if not thisOne then do solveBranch t br else return ()

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
kick :: SymbolTable → Constraint₁ → (forall s. SolverM s (String, IntGraph Label String))
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → set symbols sym def) $ do
    case c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
        newGoal b
        loop

      c → do
        newGoal c
        loop

  where
  -- | The solver loop just continuously checks the work queue,
  -- steals an item and focuses it down, until nothing remains.
  -- When the work is done it grounds the solution and returns it.
  loop :: SolverM s (String, IntGraph Label String)
  loop = do
    st ← get
    c  ← popGoal
    case c of
      Just (env, c, _) → do
        local (const env) (solveFocus c)
        loop
      Nothing → do
        -- done, gather up the solution (graph and top-level unifier)
        graph ← use graph
        graph ← liftST $ toIntGraph graph
        graph ← forM graph (\n → show <$> toTree n)
        φ     ← unifier
        return (formatUnifier φ, graph)

-- | Construct and run a solver for a constraint
solve :: SymbolTable → Constraint₁ → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymbolTable → Constraint₁ → Bool
check p c = isRight $ solve p c
