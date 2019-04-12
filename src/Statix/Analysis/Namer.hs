module Statix.Analysis.Namer where

import Control.Lens
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

import Debug.Trace

class
  ( MonadLex Ident Ident IPath m
  , MonadError TCError m
  , MonadReader NameContext m
  ) ⇒ MonadNamer m where

qualify :: MonadNamer m ⇒ Ident → m QName
qualify n = do
  mq ← view (qualifier . to (HM.lookup n))

  case mq of
    Nothing → throwError (UnboundPredicate n)
    Just q  → return q

checkTerm :: (MonadNamer m) ⇒ Term₀ → m Term₁
checkTerm = hmapM checkT
  where
    checkT :: (MonadNamer m) ⇒ TermF₀ r → m (TermF₁ r)
    checkT (TConF s ts)   = return $ TConF s ts
    checkT (TLabelF l)    = return $ TLabelF l
    checkT (TPathF n l p) = return $ TPathF n l p
    checkT (TVarF x)      = do
      p ← resolve x
      return (TVarF p)

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: (MonadNamer m) ⇒ Constraint₀ → m Constraint₁
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
checkConstraint (CData x t)        = do
  p ← resolve x
  t ← checkTerm t
  return (CData p t)
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

checkPredicate :: (MonadNamer m) ⇒ Predicate₀ → m Predicate₁
checkPredicate (Pred qn σ body) = do
  enters (fmap fst σ) $ do
    body' ← checkConstraint body
    return (Pred qn σ body')
