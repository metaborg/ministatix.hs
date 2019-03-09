{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
import Control.Monad.Except
import Control.Unification

import Statix.Syntax.Constraint
import Statix.Solver.Types
import Statix.Graph
import Statix.Graph.Types
import Statix.Graph.Paths

-- | The SolverM type implements the Binding interface from unification-fd
instance BindingMonad (TermF (STNodeRef s Label (T s))) (STU s) (SolverM s) where

  lookupVar (STVar _ r _) = do
    liftST $ readSTRef r
  
  freeVar = do
    sv     ← get
    xi     ← freshVarName
    xr     ← liftST $ newSTRef Nothing
    return (STVar xi xr ("_" ++ show xi))

  bindVar (STVar _ xr _) t = do
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

  getOutEdges (STNRef _ r) = do
    STNData es _ ← liftST (readSTRef r)
    return es

freeNamedVar :: String → SolverM s (STU s)
freeNamedVar x = do
  (STVar id r _) ← freeVar
  return (STVar id r x)

newNamedVar :: String → UTerm (TermF (STNodeRef s Label (T s))) (STU s) → SolverM s (STU s)
newNamedVar x t = do
  (STVar id r _) ← newVar t
  return (STVar id r x)

-- | Run Solver computations
runSolver :: (forall s. SolverM s a) → Either StatixError a
runSolver c = runST (runExceptT (evalStateT (runReaderT c emptyEnv) emptySolver))

-- | Lift ST computations into Solver
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift

-- | Lift State computations into Solver
liftState :: StateT (Solver s) (ExceptT StatixError (ST s)) a → SolverM s a
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
