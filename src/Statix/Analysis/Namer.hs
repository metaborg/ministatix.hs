module Statix.Analysis.Namer where

import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Data.Default
import Data.HashMap.Strict as HM
import Data.HashSet as HSet
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

checkTermF :: (MonadNamer m) ⇒ TermF₀ r → m (TermF₁ r)
checkTermF (TConF s ts)   = return $ TConF s ts
checkTermF (TLabelF l)    = return $ TLabelF l
checkTermF (TPathConsF n l p) = do
  n ← resolve n
  return $ TPathConsF n l p
checkTermF (TPathEndF n)  = do
  n ← resolve n
  return $ TPathEndF n
checkTermF (TVarF x)      = do
  p ← resolve x
  return (TVarF p)

checkTerm :: (MonadNamer m) ⇒ Term₀ → m Term₁
checkTerm = hmapM checkTermF

checkMatch  :: MonadNamer m ⇒ Matcher Term₀ → m a → m (Matcher Term₁, a)
checkMatch (Matcher _ g eqs) ma = do
  -- first extract free variables from g
  let ns = HSet.toList $ fv g

  -- introduce those variables
  enters ns $ do
    g ← checkTerm g
    a ← ma
    eqs ← forM eqs $ \(lhs, rhs) → do
      lhs ← checkTerm lhs
      rhs ← checkTerm rhs
      return (lhs, rhs)
    return (Matcher ns g eqs, a)

checkBranch :: (MonadNamer m) ⇒ Branch Term₀ Constraint₀ → m (Branch Term₁ Constraint₁) 
checkBranch (Branch m c) = do
  (m, c) ← checkMatch m (checkConstraint c)
  return (Branch m c)

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: (MonadNamer m) ⇒ Constraint₀ → m Constraint₁
checkConstraint CTrue =
  return CTrue
checkConstraint CFalse =
  return CFalse
checkConstraint (CEq t₁ t₂) = do
  t₃ ← checkTerm t₁ 
  t₄ ← checkTerm t₂
  return (CEq t₃ t₄)
checkConstraint (CAnd c d) = do
  cc ← checkConstraint c
  cd ← checkConstraint d
  return (CAnd cc cd)
checkConstraint (CEx ns c) = do
  enters ns $ do
    cc ← checkConstraint c
    return (CEx ns cc)
checkConstraint (CNew x) = do
  p ← resolve x
  return (CNew p)
checkConstraint (CData x t) = do
  p ← resolve x
  t ← checkTerm t
  return (CData p t)
checkConstraint (CEdge x l y) = do
  p ← resolve x
  q ← resolve y
  return (CEdge p l q)
checkConstraint (CQuery x re y) = do
  p ← resolve x
  q ← resolve y
  return (CQuery p re q)
checkConstraint (COne x t) = do
  p  ← resolve x
  ct ← checkTerm t
  return (COne p ct)
checkConstraint (CEvery x br) = do
  p ← resolve x
  br ← checkBranch br
  return (CEvery p br)
checkConstraint (CMin x le y) = do
  p  ← resolve x
  q  ← resolve y
  return (CMin p le q)
checkConstraint (CFilter x (MatchDatum m) y) = do
  p  ← resolve x
  q  ← resolve y
  (m, ())  ← checkMatch m (return ())
  return (CFilter p (MatchDatum m) q)
checkConstraint (CApply n ts) = do
  qn  ← qualify n
  cts ← mapM checkTerm ts
  return (CApply qn cts)
checkConstraint (CMatch t br) = do
  t  ← checkTerm t
  br ← mapM checkBranch br
  return (CMatch t br)

checkPredicate :: (MonadNamer m) ⇒ Predicate₀ → m Predicate₁
checkPredicate (Pred qn σ body) = do
  enters (fmap fst σ) $ do
    body' ← checkConstraint body
    return (Pred qn σ body')
