module Statix.Analysis.Namer where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Data.HashMap.Strict as HM
import Data.Functor.Fixedpoint
import Data.Coerce

import Statix.Syntax.Constraint
import Statix.Analysis.Types

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: Constraint RawName t → NCM (Constraint QName t)
checkConstraint = hmapM checkC 
  where
    checkC :: ConstraintF RawName t r → NCM (ConstraintF QName t r)
    -- the work
    checkC (CApplyF n ts)   = do
      qn ← qualify n
      return $ CApplyF qn ts

    -- just id
    checkC CTrueF           = return CTrueF
    checkC CFalseF          = return CFalseF
    checkC (CAndF c d)      = return (CAndF c d)
    checkC (CExF ns c)      = return (CExF ns c)
    checkC (CNewF x)        = return (CNewF x)
    checkC (CEdgeF t l s)   = return (CEdgeF t l s)
    checkC (CQueryF t re x) = return (CQueryF t re x)
    checkC (COneF x t)      = return (COneF x t)

checkPredicate :: Predicate RawName → NCM (Predicate QName)
checkPredicate (Pred σ b) = do
  b' ← checkConstraint b
  return (Pred σ b')

-- | Compute the signature of a module if it is consistent.
-- Or throw and error otherwise.
checkMod :: ModName → [Predicate RawName] → TCM Module
checkMod mname m = do
  ps  ← execStateT (mapM_ collect m) HM.empty
  let ctx = (HM.mapWithKey (\k _ → (mname, k)) ps)
  qps ← mapM (liftNC ctx . checkPredicate) ps
  return $ Mod mname qps

  where
    -- collect a signature from a raw Predicate
    collect :: Predicate RawName → StateT (HashMap RawName (Predicate RawName)) TCM ()
    collect p = do
      let name = predname $ sig p
      bound ← gets (member name)
      if bound
        then throwError $ DuplicatePredicate name
        else modify (HM.insert name p)

