module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint

import Control.Monad.Error

import Statix.Syntax.Constraint
import Statix.Analysis.Types

checkArity :: ConstraintF QName n r → TCM (ConstraintF QName n r)
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return c
checkArity c = return c

typecheck :: Constraint QName n → TCM (Constraint QName n)
typecheck = hmapM checkArity

typecheckP :: Predicate QName → TCM (Predicate QName)
typecheckP (Pred σ b) = do
  b' ← typecheck b
  return (Pred σ b')
