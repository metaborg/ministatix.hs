{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Statix.Solver.Monad where

import Prelude hiding (lookup, null)
import Data.HashMap.Strict as HM
import Data.Either
import Data.STRef
import Data.Coerce
import Data.Text
import Data.Default
import Debug.Trace

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Unique
import Control.Monad.Equiv as Equiv

import Unification as U
import Unification.ST

import Statix.Analysis.Lexical as Lex
import Statix.Syntax.Constraint
import Statix.Solver.Types
import Statix.Graph
import Statix.Graph.Types
import Statix.Graph.Paths

-- | The SolverM type implement the graph manipulation operations
instance MonadGraph (SNode s) Label (SDag s) (SolverM s) where

  newNode d = do
    ni ← fresh
    nr ← liftST $ newSTRef (STNData [] d)
    let node = STNRef ni nr
    modify (\ s → s { graph = node : graph s })
    return node

  newEdge (STNRef i r, l, y) =
    liftST $ modifySTRef r (\case STNData es d → STNData ((l , y) : es) d)
    
  getDatum (STNRef i r) = do
    STNData _ d ← liftST (readSTRef r)
    return d

  getOutEdges (STNRef _ r) = do
    STNData es _ ← liftST (readSTRef r)
    return es

instance ScopedM (SolverM s) where
  type Binder (SolverM s) = (Ident, STmRef s)
  type Ref    (SolverM s) = IPath
  type Datum  (SolverM s) = STmRef s
  
  enter     = local (\env → env { locals = HM.empty : locals env })

  intros is m = do
    frs ← asks locals
    case frs of
      (fr : frs) → local (\env → env { locals = (HM.union (HM.fromList is) fr) : frs }) m
      _          → throwError $ Panic "No frame for current scope"

  resolve p = do
    env ← asks locals
    derefLocal p env
    
    where
      derefLocal :: IPath → [Frame s] → SolverM s (STmRef s)
      derefLocal (Skip p)     (fr : frs) = derefLocal p frs
      derefLocal (Lex.End id) (fr : frs) =
        case HM.lookup id fr of
          Nothing → throwError $ Panic "Variable unbound at runtime"
          Just t  → return t
      derefLocal _ _                    =
        throwError $ Panic ":( Variable unbound at runtime"

-- | Lift the equivalence monad instance for ST to SolverM
instance MonadEquiv (STmRef s) (SolverM s) (Rep (STmRef s) (STermF s) VarInfo) where

  newClass d     = liftST $ newClass d
  description c  = liftST $ description c
  modifyDesc c d = liftST $ modifyDesc c d
  unionWith c c' f = liftST $ Equiv.unionWith c c' f
  repr c         = liftST $ repr c

instance MonadUnique Int (SolverM s) where
  fresh = do
    n ← gets nextFresh
    modify (\s → s { nextFresh = n + 1})
    return n

-- | Run Solver computations
runSolver :: (forall s. SolverM s a) → Either StatixError a
runSolver c = runST (runExceptT (evalStateT (runReaderT c def) emptySolver))

-- | Lift ST computations into Solver
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift

-- | Lift State computations into Solver
liftState :: StateT (Solver s) (ExceptT StatixError (ST s)) a → SolverM s a
liftState = lift
