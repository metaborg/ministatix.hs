module Statix.Analysis.Checker where

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans

import Data.HashMap.Strict as HM
import Data.Functor.Fixedpoint
import Data.Coerce

import Statix.Syntax.Constraint
import Statix.Analysis.Types

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: Context → Constraint RawName t → TCM (Constraint QName t)
checkConstraint ptable = cataM (checkC ptable) 
  where
    checkC :: Context → ConstraintF RawName t (Constraint QName t) → TCM (Constraint QName t)
    checkC ps (CApplyF name c) = do
      case (HM.lookup name ps) of
        Nothing   → throwError (UnboundPredicate name)
        Just pred → return $ CApply pred c
    checkC ps CTrueF  = return CTrue
    checkC ps CFalseF = return CFalse
    checkC ps (CAndF c d) = return (CAnd c d)
    checkC ps (CExF ns c) = return (CEx ns c)
    checkC ps (CNewF x) = return (CNew x)
    checkC ps (CEdgeF t l s) = return (CEdge t l s)
    checkC ps (CQueryF t re x) = return (CQuery t re x)
    checkC ps (COneF x t) = return (COne x t)

checkPredicate :: Context → Predicate RawName → TCM (Predicate QName)
checkPredicate ps (Pred σ b) = do
  b' ← checkConstraint ps b
  return (Pred σ b')

-- | Compute the signature of a module if it is consistent.
-- Or throw and error otherwise.
checkMod :: ModName → [Predicate RawName] → TCM Module
checkMod mname m = do
  ps  ← execStateT (mapM_ collect m) HM.empty
  let ctx = (HM.mapWithKey (\k _ → (mname, k)) ps)
  qps ← mapM (checkPredicate ctx) ps
  return $ Mod mname qps

  where
    -- collect a signature from a raw Predicate
    collect :: Predicate RawName → StateT (PredicateTable RawName) TCM ()
    collect p = do
      let name = predname $ sig p
      bound ← gets (member name)
      if bound
        then throwError $ DuplicatePredicate name
        else modify (HM.insert name p)
