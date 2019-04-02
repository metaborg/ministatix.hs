module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint
import Data.Default

import Control.Monad.Except

import Statix.Syntax.Constraint
import Statix.Analysis.Types

-- | Check the arity of applications against the symboltable
checkArity :: ConstraintF₁ r → TCM (ConstraintF₁ r)
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return c
checkArity c = return c

-- | Perform type checking on a constraint against the symboltable
typecheck :: Constraint₁ → TCM Constraint₁
typecheck = hmapM checkArity
