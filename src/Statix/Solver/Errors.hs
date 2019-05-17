module Statix.Solver.Errors where

import Prelude hiding (lookup, null)

import Control.Monad.Except

import Statix.Solver.Types
import Statix.Solver.Monad
import Statix.Solver.Terms

panic :: String → SolverM s a
panic s = throwError (Panic s)

-- | Throw an Unsatisfiable error containing the trace
-- as extracted from the lexical environment.
unsatisfiable :: String → SolverM s a
unsatisfiable msg = do
  trace ← getTrace
  trace ← mapM (\(qn, pos, params) → do
                   params ← mapM (instantTerm 5) params
                   return $ Call pos qn params) trace
  throwError (Unsatisfiable trace msg)

escalateUnificationError :: SolverM s a → SolverM s a
escalateUnificationError ma =
  catchError ma
    (\case
        UnificationError e → unsatisfiable $ "unification error (" ++ e ++ ")"
        e                  → throwError e
    )
