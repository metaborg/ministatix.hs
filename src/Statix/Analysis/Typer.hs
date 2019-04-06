module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint
import Data.Default

import Control.Monad.Except

import Statix.Syntax.Constraint
import Statix.Analysis.Types

-- | Get the signature of a predicate
getSig :: QName → TCM s Signature
getSig q = sig <$> getPred q

-- | Get the arity of a predicate
getArity :: QName → TCM s Int
getArity q = length <$> params <$> getSig q

-- | Check the arity of applications against the symboltable
checkArity :: ConstraintF₁ r → TCM s (ConstraintF₁ r)
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return c
checkArity c = return c

-- | Collect variable sorts from the use sites.
-- Because our sorts are simple, we don't bother with unification here.
-- checkParamSort :: ConstraintF₁ r → TCM s (ConstraintF₁ r)
-- checkParamSort c@(CNewF x) = do
--   _
-- checkParamSort c@(CEdge x l y) = do
--   _
-- checkParamSort c@(CQuery x r y) = do
--   _
-- checkParamSort c@(COne x t) =
--   _
-- checkParamSort c@(CEvery x y c') =
--   _

-- | Perform type checking on a constraint against the symboltable
typecheck :: Constraint₁ → TCM s Constraint₁
typecheck = hmapM checkArity
