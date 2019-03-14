{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Sequence as Seq
import Data.Functor.Fixedpoint
import Data.Coerce
import Data.List as List
import Data.Set as Set

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Unification

import Debug.Trace
import Unsafe.Coerce
import System.IO.Unsafe

import Statix.Regex as Re
import Statix.Syntax.Constraint
import Statix.Syntax.Terms.Reify
import Statix.Graph
import Statix.Graph.Paths
import Statix.Graph.Types
import Statix.Analysis.Symboltable
import Statix.Solver.Types
import Statix.Solver.Monad

-- | Push a constraint to the work queue
pushGoal :: C s → SolverM s ()
pushGoal c = do
  st  ← get
  env ← ask
  put (st { queue = queue st |> (env , c)})

-- | Pop a constraint to the work queue if it is non-empty
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  st ← get
  case viewl (queue st) of
    EmptyL        → return Nothing
    (c :< cs) → do
      liftState $ put (st { queue = cs })
      return (Just c)

-- | Convert a raw (closed) constraint to the internal constraint representation in ST
internalize :: Constraint QName RawTerm → C s
internalize = tmapc tintern
  where
    -- We use unsafeCoerce to lift the resulting term without nodes
    -- into the larger language with (potentially) nodes.
    tintern :: RawTerm → T s
    tintern t = unsafeCoerce $ unfreeze t

-- | Convert a raw variable (surface language name) into a unification variable.
-- If the variable is not bound, this with error.
lookupVarName :: RawName → SolverM s (T s)
lookupVarName x = do
  w ← asks (Map.lookup x . locals)
  case w of
    Just t  → return t
    Nothing → throwError (UnboundVariable x)

-- | Apply bindings of the monad to a term
-- This is a two stage conversion;
--   (1) convert raw variables to unification variables
--   (2) convert unification variables to T's using the unifier
applyLocalBindings :: T s → SolverM s (T s)
applyLocalBindings (PackT t) = do
  e  ← locals <$> ask
  let t' = cook (coerce . flip Map.lookup e) t
  return $ coerce t'

-- | Continue with the next goal
next :: SolverM s ()
next = return ()

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [RawName] → SolverM s a → SolverM s a
openExist [] c = c
openExist (n:ns) c = do
  v ← freeNamedVar n
  local (insertLocal n (PackT $ UVar v)) (openExist ns c)

checkCritical :: Map (STN s) (Regex Label) → C s → SolverM s (Set (STN s, Label))
checkCritical ces c = cataM check c
  where
    check (CAndF l r) = return (l `Set.union` r)
    check (CExF xs c) = return c
    check (CEdgeF t₁ l t₂) = do
      t₁ ← applyLocalBindings t₁ >>= applyBindings . coerce
      case t₁ of
        (Node n) → 
          case ces Map.!? n of
            Nothing  → return Set.empty
            Just re  → if not $ Re.empty $ match l re then return $ Set.singleton (n, l) else return Set.empty
        _ → return Set.empty
    check (CApplyF p ts) = return Set.empty -- TODO!
    check _ = return Set.empty

queryGuard :: Map (STN s) (Regex Label) → SolverM s (Set (STN s, Label))
queryGuard ce = do
  cs ← liftState $ gets queue
  Set.unions <$> mapM (\(e, c) → local (const e) $ checkCritical ce c) cs

-- | Try to solve a focused constraint
solveFocus :: C s → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (Unsatisfiable "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← applyLocalBindings t1
  t2' ← applyLocalBindings t2
  _ ← unifyOccurs (coerce t1') (coerce t2') {- TODO unify -}
  next

solveFocus (CAnd l r) = do
  pushGoal r
  solveFocus l

solveFocus (CEx ns c) = do
  openExist ns (solveFocus c)

solveFocus (CNew t) = do
  t' ← applyLocalBindings t
  u  ← newNode Nothing
  catchError
    (unify (coerce t') (Node u))
    (\ err → throwError (Unsatisfiable "Not fresh!"))
  next

solveFocus (CEdge t₁ l t₂) = do
  t₁' ← applyLocalBindings t₁ >>= applyBindings . coerce
  t₂' ← applyLocalBindings t₂ >>= applyBindings . coerce
  case (coerce t₁' , coerce t₂') of
    (Node n, Node m) → newEdge (n, l, m)
    (UVar x, _)      → pushGoal (CEdge (coerce t₁') l (coerce t₂'))
    (_ , UVar x)     → pushGoal (CEdge (coerce t₁') l (coerce t₂'))
    otherwise        → throwError TypeError

solveFocus (CQuery t r x) = do
  -- instantiate
  t' ← applyLocalBindings t >>= applyBindings . coerce
  b  ← lookupVarName x

  -- check if t' is sufficiently instantiated
  case t' of
    -- If the source node is ground
    -- then we can attempt to solve the query
    (Node n)  → do
      -- first we check the guard
      es ← findReachable n r
      stuckOn ← queryGuard es

      if List.null stuckOn then do
        -- if it passes we solve the query
        ans ← runQuery n r
        unify (coerce b) (Answer ans)
        next
      else do
        pushGoal (trace "Delaying query" $ CQuery (PackT t') r x)
        next

    (UVar _)  → pushGoal (CQuery (PackT t') r x)
    otherwise → throwError TypeError

solveFocus c@(COne x t) = do
  -- instantiate
  t       ← applyLocalBindings t >>= applyBindings . coerce
  v       ← lookupVarName x
  ans     ← applyBindings (coerce v)
  case ans of
    (UVar x)          → pushGoal c
    (Answer (p : [])) → do unify t (reify p); return ()
    (Answer [])       → throwError (Unsatisfiable $ show c ++ " (No paths)")
    (Answer ps)       → throwError (Unsatisfiable $ show c ++ " (More than one path: " ++ show ps ++ ")")
    _                 → throwError (Unsatisfiable $ show c ++ " (" ++ show ans ++ " is not an answer set)")

solveFocus (CApply p ts) = do
   mp ← getPredicate p <$> ask
   case mp of
     Just (Pred σ c) → do
       -- normalize the parameters
       ts' ← mapM applyLocalBindings ts

       -- bind the parameters
       local (\(Env ps _) → Env ps (Map.fromList $ List.zip (params σ) ts')) $
         -- convert the body to the internal representation
         let c' = internalize c in

         -- solve the body
         solveFocus c'

     Nothing → error "Panic! Encountered unbound predicate"

-- | A simple means to getting a unifier out of State, convert everything to a string
showUnifier :: SolverM s String
showUnifier = do
  e  ← locals <$> ask
  ts ← mapM formatBinding (Map.toList e)
  return (intercalate "\n" ts)
  where
    formatBinding (k, b) = do
      b ← applyBindings (coerce b)
      return $ "  " ++ k ++ " ↦ " ++ (show b)

-- | Construct a solver for a raw constraint
kick :: SymbolTable → Constraint QName RawTerm → (forall s. SolverM s (String, IntGraph Label String))
kick p c =
  -- convert the raw constraint to the internal representatio
  local (\_ → Env p Map.empty) $ do
    case internalize c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
        pushGoal b
        loop
      c → do
        pushGoal c
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
      Just (env , c) → do
        local (const env) (solveFocus c)
        loop
      Nothing → do
        -- done, gather up the solution (graph and top-level unifier)
        s ← get
        g ← liftST $ toIntGraph (graph s)
        φ ← showUnifier
        return (φ, fmap show g)

-- | Construct and run a solver for a constraint
solve :: SymbolTable → Constraint QName RawTerm → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymbolTable → Constraint QName RawTerm → Bool
check p c = isRight $ solve p c
