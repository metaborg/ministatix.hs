module Statix.Solver.Debug where

import Data.HashMap.Strict
import Data.Foldable as Fold
import Data.List as List
import Data.Maybe

import Control.Lens
import Control.Monad.Reader

import Statix.Graph
import Statix.Syntax
import Statix.Solver.Types
import Statix.Solver.Monad
import Statix.Solver.Terms

import Unification as U hiding (TTm)

import Debug.Trace

__trace__ = False

tracer :: String → a → a
tracer s a = if __trace__ then trace s a else a

-- | get the first enclosing predicate from the environment trace
-- if there is any
enclosingPred :: Env s → Maybe QName
enclosingPred env =
  let xs = fmap desc (env^.locals) in
    listToMaybe $ concatMap (\case
                                FrExist     → []
                                FrPred name → [name]
                            ) xs

formatGoal :: Goal s → SolverM s String
formatGoal (env, c, _) = do
  local (const env) $ do
    let qn = enclosingPred env
    cs ← instantConstraint 5 c
    case qn of
      Just qn → return $ cs ++ " (in " ++ showQName qn ++ ")"
      Nothing → return cs

-- | User "friendly" string representation of the solver queue
formatQueue :: SolverM s [String]
formatQueue = do
  q ← use queue
  mapM formatGoal (Fold.toList q)

tracerWithQueue :: SolverM s a → SolverM s a
tracerWithQueue c = do
  q ← formatQueue
  let q' = fmap show q
  tracer (intercalate "\n, " q') c

dumpgraph =  do
  gr ← use graph
  gr ← liftST $ toIntGraph gr
  mapM (instantTerm 5) gr

type Unifier s = HashMap Ident (STree s)

-- | A simple means to getting a unifier out of ST, convert everything to a string
unifier :: SolverM s (Unifier s)
unifier = do
  env ← view locals
  mapM toTree (binders $ head env)
