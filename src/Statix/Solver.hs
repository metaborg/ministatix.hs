{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.HashMap.Strict as HM
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Sequence as Seq
import Data.Functor.Fixedpoint
import Data.List as List
import Data.Set as Set
import qualified Data.Text as Text

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Debug.Trace

import Statix.Regex as Re
import Statix.Syntax.Constraint
import Statix.Graph
import Statix.Graph.Paths
import Statix.Graph.Types
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical
import Statix.Solver.Types
import Statix.Solver.Reify
import Statix.Solver.Monad

-- | Push a constraint to the work queue
pushGoal :: Constraint₁ → SolverM s ()
pushGoal c = do
  st  ← get
  env ← ask
  put (st { queue = queue st |> (env , c)})

-- | Pop a constraint to the work queue if it is non-empty
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  st ← get
  case viewl (queue st) of
    EmptyL    → return Nothing
    (c :< cs) → do
      liftState $ put (st { queue = cs })
      return (Just c)

-- | Continue with the next goal
next :: SolverM s ()
next = return ()

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [Param] → SolverM s a → SolverM s a
openExist ns c = do
  let ids = fmap pname ns
  bs ← mapM (\i → do v ← freshUvar i Nothing; return (i, SVar v)) ids
  enters bs c

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → SolverM s (Set (SNode s, Label))
checkCritical ces c = cataM check c
  where
    check (CAndF l r) = return (l `Set.union` r)
    check (CExF xs c) = return c
    check (CEdgeF x l y) = do
      t₁ ← resolve x
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
  Set.unions <$> mapM (\(e, c) → local (const e) $ checkCritical ce c) cs

instantiate :: Term₁ → SolverM s (STerm s)
instantiate (Var p)    = resolve p
instantiate (Con c ts) = do
  ts' ← mapM instantiate ts
  return (SCon c ts')
instantiate (Label l)  = return (SLabel l)

occursCheck :: MVar s → STerm s → Bool
occursCheck u (SVar v)    = u == v
occursCheck u (SCon c ts) = all (occursCheck u) ts
occursCheck u _           = False

unifyVar :: MVar s → STerm s → SolverM s (STerm s)
unifyVar u t = do
  b ← liftST $ readSTRef (ref u)
  case b of
    Just t' → unify t' t
    Nothing → do
      if occursCheck u t
      then do
        liftST $ writeSTRef (ref u) (Just t)
        return t
      else throwError (Unsatisfiable "Occurs check failed")

unify :: STerm s → STerm s → SolverM s (STerm s)
unify (SVar u) r = unifyVar u r
unify l (SVar u) = unifyVar u l
unify (SNode n) (SNode m)
  | n == m    = return $ SNode n
  | otherwise = throwError (Unsatisfiable "Unification failed")
unify (SCon c xs) (SCon d ys)
  | c == d = do
    ts ← zipWithM unify xs ys
    return (SCon c ts)
  | otherwise = throwError (Unsatisfiable "Unification failed")

-- unification on answer sets is prohibited
unify (SAns _) _ = throwError TypeError
unify _ (SAns _) = throwError TypeError
  
-- | Try to solve a focused constraint
solveFocus :: Constraint₁ → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (Unsatisfiable "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← instantiate t1
  t2' ← instantiate t2
  unify t1' t2'
  next

solveFocus (CAnd l r) = do
  pushGoal r
  solveFocus l

solveFocus (CEx ns c) = do
  openExist ns (solveFocus c)

solveFocus (CNew x) = do
  t  ← resolve x
  u  ← newNode Nothing
  catchError
    (unify t (SNode u))
    (\ err → throwError (Unsatisfiable "Not fresh!"))
  next

solveFocus c@(CEdge x l y) = do
  t₁ ← resolve x
  t₂ ← resolve y
  case (t₁ , t₂) of
    (SNode n, SNode m) → newEdge (n, l, m)
    (SVar _, _)        → pushGoal c
    (_ , SVar _)       → pushGoal c
    otherwise          → throwError TypeError

solveFocus c@(CQuery x r y) = do
  t ← resolve x
  case t of
    -- If the source node is ground
    -- then we can attempt to solve the query
    (SNode n)  → do
      -- first we check the guard
      es ← findReachable n r
      stuckOn ← queryGuard es

      if List.null stuckOn then do
        -- if it passes we solve the query
        ans ← runQuery n r
        b   ← resolve y
        unify b (SAns ans)
        next
      else do
        pushGoal (trace "Delaying query" c)
        next

    (SVar _)  → pushGoal c
    otherwise → throwError TypeError

solveFocus c@(COne x t) = do
  t ← resolve x
  case t of
    (SVar x)        → pushGoal c
    (SAns (p : [])) → do unify (reify p) t ; return ()
    (SAns [])       → throwError (Unsatisfiable $ show c ++ " (No paths)")
    (SAns ps)       → throwError (Unsatisfiable $ show c ++ " (More than one path: " ++ show ps ++ ")")
    _               → throwError TypeError

solveFocus (CApply p ts) = do
   mp ← getPredicate p <$> ask
   case mp of
     Just (Pred σ c) → do
       -- normalize the parameters
       ts' ← mapM instantiate ts

       -- bind the parameters
       enters (List.zip (fmap pname $ params σ) ts') $ do
         -- solve the body
         solveFocus c

     Nothing → error "Panic! Encountered unbound predicate"

-- | A simple means to getting a unifier out of ST, convert everything to a string
showUnifier :: SolverM s String
showUnifier = do
  e  ← locals <$> ask
  return $ formatFrame (head e)
  where
    formatFrame :: Frame s → String
    formatFrame fr = do
      List.foldl (\s (k, t) → "  " ++ Text.unpack k ++ " ↦ " ++ (show t)) "" (HM.toList fr)

-- | Construct a solver for a raw constraint
kick :: SymTab → Constraint₁ → (forall s. SolverM s (String, IntGraph Label String))
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → emptyEnv { symbols = sym }) $ do
    case c of
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
solve :: SymTab → Constraint₁ → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymTab → Constraint₁ → Bool
check p c = isRight $ solve p c
