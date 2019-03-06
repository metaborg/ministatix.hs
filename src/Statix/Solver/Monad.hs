{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Solver.Monad where

import Prelude hiding (lookup, null)
import Data.Map.Strict hiding (map, null)
import qualified Data.Map.Strict as Map
import Data.Either
import Data.STRef
import Data.Coerce

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Unification

import Statix.Syntax.Constraint
import Statix.Solver.Types
import Statix.Graph

-- | The SolverM type implements the Binding interface from unification-fd
instance BindingMonad (TermF (STNodeRef s Label (T s))) (STU s) (SolverM s) where
  lookupVar (STVar i r) = do
    liftST $ readSTRef r

  newVar t = do
    xi     ← freshVarName
    xr     ← liftST $ newSTRef (Just t)
    return (STVar xi xr)
  
  freeVar = do
    sv     ← get
    xi     ← freshVarName
    xr     ← liftST $ newSTRef Nothing
    return (STVar xi xr)

  bindVar (STVar _ xr) t = do
    liftST $ writeSTRef xr (Just t)

-- | The SolverM type implement the graph manipulation operations
instance MonadGraph (STNodeRef s Label (T s)) Label (T s) (SolverM s) where

  newNode d = do
    ni ← freshNodeName
    nr ← liftST $ newSTRef (STNData [] d)
    let node = STNRef ni nr
    modify (\ s → s { graph = node : graph s })
    return node

  newEdge (STNRef i r, l, y) =
    liftST $ modifySTRef r (\case STNData es d → STNData ((l , y) : es) d)
    
  getDatum (STNRef i r) = do
    STNData _ d ← liftST (readSTRef r)
    return d

  runQuery n re = do
    liftST $ resolve n re

-- | Run Solver computations
runSolver :: (forall s. SolverM s a) → Either StatixError a
runSolver c = runST (runErrorT (evalStateT (runReaderT c Map.empty) emptySolver))

-- | Lift ST computations into Solver
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift

-- | Lift State computations into Solver
liftState :: StateT (Solver s) (ErrorT StatixError (ST s)) a → SolverM s a
liftState = lift

-- | Get a fresh variable identifier
freshVarName :: SolverM s Int
freshVarName = do
  s ← get
  let n = nextU s
  put (s { nextU = n + 1})
  return n
  
-- | Get a fresh node identifier
freshNodeName :: SolverM s Int
freshNodeName = do
  s ← get
  let n = nextN s
  put (s { nextN = n + 1})
  return n
