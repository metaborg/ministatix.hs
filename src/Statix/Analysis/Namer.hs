module Statix.Analysis.Namer where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Data.Default
import Data.HashMap.Strict as HM
import Data.Functor.Fixedpoint
import Data.Coerce
import Data.Text

import Statix.Syntax.Constraint
import Statix.Analysis.Types
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical

checkTerm :: Term₀ → NCM Term₁
checkTerm = hmapM checkT
  where
    checkT :: TermF₀ r → NCM (TermF₁ r)
    checkT (TConF s ts)   = return $ TConF s ts
    checkT (TLabelF l)    = return $ TLabelF l
    checkT (TVarF x)      = do
      p ← resolve x
      return (TVarF p)

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: Constraint₀ → NCM Constraint₁
checkConstraint CTrue           = return CTrue
checkConstraint CFalse          = return CFalse
checkConstraint (CAnd c d)      = do
  cc ← checkConstraint c
  cd ← checkConstraint d
  return (CAnd cc cd)
checkConstraint (CEx ns c)      = do
  enters (fmap pname ns) $ do
    cc ← checkConstraint c
    return (CEx ns cc)
checkConstraint (CNew x)        = do
  p ← resolve x
  return (CNew p)
checkConstraint (CEdge x l y)   = do
  p ← resolve x
  q ← resolve y
  return (CEdge p l q)
checkConstraint (CQuery x re y) = do
  p ← resolve x
  q ← resolve y
  return (CQuery p re q)
checkConstraint (COne x t)      = do
  p  ← resolve x
  ct ← checkTerm t
  return (COne p ct)
checkConstraint (CApply n ts)   = do
  qn  ← qualify n
  cts ← mapM checkTerm ts
  return $ CApply qn cts

checkPredicate :: Predicate₀ → NCM Predicate₁
checkPredicate (Pred σ body) = do
  enters (fmap pname $ params σ) $ do
    body' ← checkConstraint body
    return (Pred σ body')

-- | Compute the signature of a module if it is consistent.
checkMod :: Ident → [Predicate₀] → NCM (Module IPath Term₁)
checkMod mname m = do
  -- collect signatures and bind them in the context
  ps      ← execStateT (mapM_ collect m) HM.empty
  let ctx = HM.mapWithKey (\k _ → (mname, k)) ps

  -- check predicates for wellboundness of applications
  local (\_ → def { qualifier = ctx }) $ do
    qps ← mapM checkPredicate ps
    return $ Mod mname qps

  where
    -- | Collect a signature from a raw Predicate.
    -- Checks against duplicate definitions.
    collect :: Predicate₀ → StateT (HashMap Ident Predicate₀) NCM ()
    collect p = do
      let name = predname $ sig p
      bound ← gets (member name)
      if bound
        then throwError $ DuplicatePredicate name
        else modify (HM.insert name p)
