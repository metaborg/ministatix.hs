module Statix.Analysis.Namer where

import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Data.HashMap.Strict as HM
import Data.HashSet as HSet
import Data.Functor.Fixedpoint

import Statix.Syntax
import Statix.Analysis.Types
import Statix.Analysis.Lexical

class
  ( MonadLex Ident Ident IPath m
  , MonadError TCError m
  , MonadReader NameContext m
  , FrameDesc m ~ ()
  ) ⇒ MonadNamer m where

qualify :: MonadNamer m ⇒ Ident → m QName
qualify n = do
  mq ← view (qualifier . to (HM.lookup n))

  case mq of
    Nothing → throwError (UnboundPredicate n)
    Just q  → return q

checkTermF :: (MonadNamer m) ⇒ TermF₀ r → m (TermF₁ r)
checkTermF (TTmF at)      = return $ TTmF at
checkTermF (TLabelF l t)  = do
  return $ TLabelF l t
checkTermF (TPathConsF n l p) = do
  return $ TPathConsF n l p
checkTermF (TPathEndF n)  = do
  return $ TPathEndF n
checkTermF (TVarF x)      = do
  p ← resolve x
  return (TVarF p)

checkTerm :: (MonadNamer m) ⇒ Term₀ → m Term₁
checkTerm = hmapM checkTermF

checkGuard  :: MonadNamer m ⇒ Guard Term₀ → m (Guard Term₁)
checkGuard (GEq lhs rhs) = do
  lhs ← checkTerm lhs
  rhs ← checkTerm rhs
  return $ GEq lhs rhs
checkGuard (GNotEq lhs rhs) = do
  lhs ← checkTerm lhs
  rhs ← checkTerm rhs
  return $ GNotEq lhs rhs

checkMatch  :: MonadNamer m ⇒ Matcher Term₀ → m a → m (Matcher Term₁, a)
checkMatch (Matcher _ g eqs) ma = do
  -- first extract free variables from g
  let ns = HSet.toList $ fv g

  -- introduce those variables
  enters () ns $ do
    g ← checkTerm g
    a ← ma
    eqs ← forM eqs checkGuard
    return (Matcher ns g eqs, a)

checkBrannch :: (MonadNamer m) ⇒ Branch Term₀ Constraint₀ → m (Branch Term₁ Constraint₁) 
checkBrannch (Branch m c) = do
  (m, c) ← checkMatch m (checkConstraint c)
  return (Branch m c)

-- Convert a constraint with unqualified predicate names
-- to one with qualified predicate names
checkConstraint :: (MonadNamer m) ⇒ Constraint₀ → m Constraint₁
checkConstraint (CTrue ann)  = return $ CTrue ann
checkConstraint (CFalse ann) = return $ CFalse ann
checkConstraint (CEq ann t₁ t₂) = do
  t₃ ← checkTerm t₁ 
  t₄ ← checkTerm t₂
  return (CEq ann t₃ t₄)
checkConstraint (CNotEq ann t₁ t₂) = do
  t₃ ← checkTerm t₁ 
  t₄ ← checkTerm t₂
  return (CNotEq ann t₃ t₄)
checkConstraint (CAnd ann c d) = do
  cc ← checkConstraint c
  cd ← checkConstraint d
  return (CAnd ann cc cd)
checkConstraint (CEx ann ns c) = do
  enters () ns $ do
    cc ← checkConstraint c
    return (CEx ann ns cc)
checkConstraint (CNew ann x t) = do
  p ← resolve x
  t ← checkTerm t
  return (CNew ann p t)
checkConstraint (CData ann x t) = do
  p ← resolve x
  t ← checkTerm t
  return (CData ann p t)
checkConstraint (CEdge ann x l y) = do
  p ← resolve x
  q ← resolve y
  l ← checkTerm l
  return (CEdge ann p l q)
checkConstraint (CQuery ann x re y) = do
  p ← resolve x
  q ← resolve y
  return (CQuery ann p re q)
checkConstraint (COne ann x t) = do
  p  ← resolve x
  ct ← checkTerm t
  return (COne ann p ct)
checkConstraint (CNonEmpty ann x) = do
  p  ← resolve x
  return (CNonEmpty ann p)
checkConstraint (CEvery ann x br) = do
  p ← resolve x
  br ← checkBrannch br
  return (CEvery ann p br)
checkConstraint (CMin ann x le y) = do
  p  ← resolve x
  q  ← resolve y
  return (CMin ann p le q)
checkConstraint (CFilter ann x (MatchDatum m) y) = do
  p  ← resolve x
  q  ← resolve y
  (m, ())  ← checkMatch m (return ())
  return (CFilter ann p (MatchDatum m) q)
checkConstraint (CApply ann n ts) = do
  qn  ← qualify n
  cts ← mapM checkTerm ts
  return (CApply ann qn cts)
checkConstraint (CMatch ann t br) = do
  t  ← checkTerm t
  br ← mapM checkBrannch br
  return (CMatch ann t br)

checkPredicate :: (MonadNamer m) ⇒ Predicate₀ → m Predicate₁
checkPredicate (Pred ann qn σ body) = do
  enters () σ $ do
    body' ← checkConstraint body
    return (Pred ann qn σ body')
