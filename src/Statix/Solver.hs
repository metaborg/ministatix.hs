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

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Trans
import Control.Unification

import Debug.Trace
import Unsafe.Coerce

import Statix.Syntax.Constraint
import Statix.Syntax.Terms.Reify
import Statix.Graph
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

-- | Convert a raw constraint to the internal constraint representation in ST
internalize :: RawConstraint → C s
internalize c = cata _intern c
  where
    -- We use unsafeCoerce to lift the resulting term without nodes
    -- into the larger language with (potentially) nodes.
    tintern :: RawTerm → T s
    tintern t = unsafeCoerce $ unfreeze t

    _intern :: ConstraintF RawTerm (C s) → C s
    _intern (CEqF t₁ t₂) = CEq (tintern t₁) (tintern t₂)
    _intern (CNewF t) = CNew (tintern t)
    _intern (CEdgeF t₁ l t₂) = CEdge (tintern t₁) l (tintern t₂)
    _intern CTrueF = CTrue
    _intern CFalseF = CFalse
    _intern (CAndF c d) = CAnd c d
    _intern (CExF ns c) = CEx ns c
    _intern (CQueryF t r x) = CQuery (tintern t) r x
    _intern (COneF x t) = COne x (tintern t)
    _intern (CApplyF p ts) = CApply p (fmap tintern ts)

-- | Convert a raw variable (surface language name) into a unification variable.
-- If the variable is not bound, this with error.
lookupVarName :: VarName → SolverM s (T s)
lookupVarName x = do
  w ← asks (Map.lookup x . locals)
  case w of
    Just t  → return t
    Nothing → throwError (UnboundVariable x)

-- | Apply bindings of the monad to a term
-- This is a two stage conversion;
--   (1) convert raw variables to unification variables
--   (2) convert unification variables to T's using the unifier
subst :: T s → SolverM s (T s)
subst (PackT t) = do
  e  ← locals <$> ask
  let t' = cook (coerce . flip Map.lookup e) t
  return $ coerce t'

-- | Continue with the next goal
next :: SolverM s ()
next = return ()

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [VarName] → SolverM s a → SolverM s a
openExist [] c = c
openExist (n:ns) c = do
  v ← freeNamedVar n
  local (insertLocal n (PackT $ UVar v)) (openExist ns c)

-- | Try to solve a focused constraint
solveFocus :: C s → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (UnsatisfiableError "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← subst t1
  t2' ← subst t2
  _ ← unifyOccurs (coerce t1') (coerce t2') {- TODO unify -}
  next

solveFocus (CAnd l r) = do
  pushGoal r
  solveFocus l

solveFocus (CEx ns c) = do
  openExist ns (solveFocus c)

solveFocus (CNew t) = do
  t' ← subst t
  u  ← newNode Nothing
  catchError
    (unify (coerce t') (Node u))
    (\ err → throwError (UnsatisfiableError "Not fresh!"))
  next

solveFocus (CEdge t₁ l t₂) = do
  t₁' ← subst t₁
  t₂' ← subst t₂
  case (coerce t₁' , coerce t₂') of
    (Node n, Node m) → newEdge (n, l, m)
    (UVar x, _)      → pushGoal (CEdge t₁' l t₂')
    (_ , UVar x)     → pushGoal (CEdge t₁' l t₂')
    otherwise        → throwError TypeError

solveFocus (CQuery t r x) = do
  -- instantiate
  PackT t' ← subst t
  b        ← lookupVarName x

  -- check if t' is sufficiently instantiated
  case t' of
    (Node n)  → do
      ans ← runQuery n r
      unify (coerce b) (Answer ans)
      next
    (UVar _)  → pushGoal (CQuery (PackT t') r x)
    otherwise → throwError TypeError

solveFocus c@(COne x t) = do
  -- instantiate
  PackT t ← subst t
  v       ← lookupVarName x
  ans     ← applyBindings (coerce v)
  case ans of
    (Answer (p : [])) → do unify t (reify p); return ()
    (Answer [])       → throwError (UnsatisfiableError $ show c ++ " (No paths)")
    (Answer ps)       → throwError (UnsatisfiableError $ show c ++ " (More than one path: " ++ show ps ++ ")")
    _                 → throwError (UnsatisfiableError $ show c ++ " (Not an answer set)")

solveFocus (CApply p ts) = do
   mp ← getPredicate p <$> ask
   case mp of
     Just (Pred _ ns c) → do
       -- normalize the parameters
       ts' ← mapM subst ts

       -- bind the parameters
       local (\(Env ps _) → Env ps (Map.fromList $ List.zip ns ts')) $
         -- convert the body to the internal representation
         let c' = internalize c in

         -- solve the body
         solveFocus c'

     Nothing → throwError $ UnboundVariable p

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
kick :: Program → Constraint RawTerm → (forall s. SolverM s (String, IntGraph Label String))
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
solve :: Program → Constraint RawTerm → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: Program → Constraint RawTerm → Bool
check p c = isRight $ solve p c
