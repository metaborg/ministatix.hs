{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Statix.Solver.Monad where

import Prelude hiding (lookup, null)
import Data.HashMap.Strict as HM
import Data.Either
import Data.STRef
import Data.Coerce
import Data.Default
import Data.Hashable
import Data.Maybe

import Control.Lens
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Unique
import Control.Monad.Equiv as Equiv

import Unification as U
import Unification.ST

import Statix.Analysis.Lexical as Lex
import Statix.Analysis.Symboltable
import Statix.Syntax.Constraint
import Statix.Solver.Types
import Statix.Graph
import Statix.Graph.Types
import Statix.Graph.Paths

-- | The SolverM type implement the graph manipulation operations
instance MonadGraph (SNode s) Label (STmRef s) (SolverM s) where

  newNode d = do
    ni ← fresh :: SolverM s Integer
    nr ← liftST $ newSTRef (STNData [] d)
    let node = STNRef (hash ni) nr
    graph %= (node:)
    return node

  newEdge (STNRef i r, l, t, y) =
    liftST $ modifySTRef r (\case STNData es d → STNData ((l, t, y) : es) d)
    
  getDatum (STNRef i r) = do
    STNData _ d ← liftST (readSTRef r)
    return d

  setDatum (STNRef i r) d = do
    liftST $ modifySTRef r (\case STNData es _ → STNData es (Just d))

  getOutEdges (STNRef _ r) = do
    STNData es _ ← liftST (readSTRef r)
    return es

instance MonadLex (Ident, STmRef s) IPath (STmRef s) (SolverM s) where
  type FrameDesc (SolverM s) = Trace

  enter fd = local (\env → env { _locals = def { desc = fd } : _locals env })

  intros is m = do
    frs ← view locals
    case frs of
      (fr : frs) → do
        let fr' = fr { binders = HM.union (HM.fromList is) (binders fr) }
        local (\env → env { _locals = fr' : frs }) m
      _          → throwError $ Panic "No frame for current scope"

  resolve p = do
    env ← view locals
    derefLocal p env
    
    where
      derefLocal :: IPath → [Frame s] → SolverM s (STmRef s)
      derefLocal (Skip p)     (fr : frs) = derefLocal p frs
      derefLocal (Lex.End id) (fr : frs) =
        case HM.lookup id (binders fr) of
          Nothing → throwError $ Panic $ "Variable " ++ show id ++ " unbound at runtime"
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

instance MonadUnique Integer (SolverM s) where
  fresh = do
    n ← use nextFresh
    nextFresh %= (+1)
    return n

  updateSeed i = modify (set nextFresh i)

instance MonadUnify (STermF s) (STmRef s) VarInfo StatixError (SolverM s)

getPredicate :: (MonadReader (Env s) m) ⇒ QName → m Predicate₁
getPredicate qn = view (symbols . to (!!! qn))

-- | Run Solver computations
runSolver :: (forall s. SolverM s a) → (Either StatixError a, IntGraph Label String)
runSolver c = runST $ do
  (c, s) ← runStateT (runExceptT (runReaderT c def)) def
  graph ← toIntGraph (_graph s)
  graph ← forM graph (\n → show <$> toTree n)
  return (c, graph)

-- | Get a trace entry from a frame
getCallTrace :: Frame s → SolverM s (Maybe (QName , [STmRef s]))
getCallTrace fr = case desc fr of
  FrExist   → return Nothing
  FrPred qn → do
      σ ← sig <$> getPredicate qn
      let bs = fmap (\(id, _) → (binders fr) HM.! id) σ
      return $ Just (qn, bs)

-- | Create a trace from the callstack
getTrace :: SolverM s [(QName , [STmRef s])]
getTrace = do
  env ← view locals
  catMaybes <$> mapM getCallTrace env

-- | Lift ST computations into Solver
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift
