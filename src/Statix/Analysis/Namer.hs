module Statix.Analysis.Namer where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Data.Default
import Data.HashMap.Strict as HM
import Data.Functor.Fixedpoint
import Data.Coerce
import qualified Data.Text as Text

import Statix.Syntax.Constraint
import Statix.Analysis.Types
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical

instance ScopedM NCM where
  type Binder NCM = Ident
  type Ref    NCM = Ident
  type Datum  NCM = IPath

  enter c     = local (\ctx → ctx { locals = [] : locals ctx }) c

  intros xs c = local (\ctx →
                       let lex = locals ctx
                       in ctx { locals = (xs ++ head lex) : tail lex }) c

  resolve x   = do
    lex ← asks locals
    search x lex

    where
      search :: Text.Text → [[Ident]] → NCM IPath
      search x [] = throwError (UnboundVariable x)
      search x (xs : xss) =
        if elem x xs
          then return (End x)
          else do
            p ← search x xss
            return (Skip p)

checkTerm :: Term₀ → NCM Term₁
checkTerm = hmapM checkT
  where
    checkT :: TermF₀ r → NCM (TermF₁ r)
    checkT (TConF s ts)   = return $ TConF s ts
    checkT (TLabelF l)    = return $ TLabelF l
    checkT (TPathF n l p) = return $ TPathF n l p
    checkT (TVarF x)      = do
      p ← resolve x
      return (TVarF p)

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: Constraint₀ → NCM Constraint₁
checkConstraint CTrue           = return CTrue
checkConstraint CFalse          = return CFalse
checkConstraint (CEq t₁ t₂)     = do
  t₃ ← checkTerm t₁ 
  t₄ ← checkTerm t₂
  return (CEq t₃ t₄)
checkConstraint (CAnd c d)      = do
  cc ← checkConstraint c
  cd ← checkConstraint d
  return (CAnd cc cd)
checkConstraint (CEx ns c)      = do
  enters ns $ do
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
checkConstraint (CEvery x y c)    = do
  p ← resolve y
  enters [ x ] $ do
    c ← checkConstraint c
    return (CEvery x p c)
checkConstraint (CApply n ts)   = do
  qn  ← qualify n
  cts ← mapM checkTerm ts
  return $ CApply qn cts

checkPredicate :: Predicate₀ → NCM Predicate₁
checkPredicate (Pred qn σ body) = do
  enters (fmap fst σ) $ do
    body' ← checkConstraint body
    return (Pred qn σ body')

-- | Compute the signature of a module if it is consistent.
checkMod :: Ident → [Predicate₀] → NCM Module
checkMod mname m = do
  -- collect signatures and bind them in the context
  ps      ← execStateT (mapM_ collect m) HM.empty
  let ctx = HM.mapWithKey (\k _ → (mname, k)) ps

  -- check predicates for wellboundness of applications
  local (\_ → def { qualifier = ctx }) $ do
    qps ← mapM checkPredicate ps
    return $ qps

  where
    -- | Collect a signature from a raw Predicate.
    -- Checks against duplicate definitions.
    collect :: Predicate₀ → StateT (HashMap Ident Predicate₀) NCM ()
    collect p = do
      let name = snd $ qname p
      bound ← gets (member name)
      if bound
        then throwError $ DuplicatePredicate name
        else modify (HM.insert name p)
