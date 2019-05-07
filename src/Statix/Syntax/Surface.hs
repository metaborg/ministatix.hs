-- | The surface syntax is defined literally as an extension of the core
-- constraint language using Data.Functor.Sum and then taking the fixedpoint.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
module Statix.Syntax.Surface where

import Data.Functor.Fixedpoint
import Data.Functor.Sum

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Unique
import Control.Monad.Writer.Strict hiding (Sum)

import Statix.Syntax.Types
import Statix.Syntax.Terms
import Statix.Syntax.Typing
import Statix.Syntax.Constraint hiding (Matcher, Branch, PathFilter(..))
import qualified Statix.Syntax.Constraint as Syn

import ATerms.Syntax.ATerm

data Pattern
  = PatTm (TermF₀ Pattern)
  | Wildcard deriving (Show)

funcPat c ts = PatTm (TTmF (AFuncF c ts))
consPat t ts = PatTm (TTmF (AConsF t ts))
nilPat       = PatTm (TTmF ANilF)
tuplePat ts  = PatTm (TTmF (ATupleF ts))
unitPat      = PatTm (TTmF (ATupleF []))

data Matcher    = Matcher [Ident] Pattern [(Term₀ , Term₀)] deriving (Show)
data Branch c   = Branch Matcher c deriving (Functor, Foldable, Traversable, Show)
data PathFilter = MatchDatum Matcher

data Extensions r
  = SMatchF Term₀ [Branch r]
  | SFilterF Ident PathFilter Ident
  | SEveryF Ident (Branch r)
  deriving (Functor, Foldable, Traversable)

-- | The surface syntax consists of the core constraint language
-- plus some extensions
type SurfaceCF = Sum (ConstraintF Ident Ident Term₀) Extensions
type SurfaceC  = Fix SurfaceCF
type SurfaceP  = Predicate SurfaceC
type SurfaceM  = RawModule SurfaceC

desugar :: SurfaceC → Constraint Ident Ident Term₀
desugar c = evalState (cataM desugarF c) 0

desugarPred :: SurfaceP → Predicate₀
desugarPred (Pred qn sig body) = Pred qn sig (desugar body)

desugarMod :: SurfaceM → RawModule₀
desugarMod (Mod name imps defs) = Mod name imps (fmap desugarPred defs)

-- | Implementation of desguaring

type DesugarM = StateT Integer (Writer [Ident])

desugarF :: SurfaceCF (Constraint Ident Ident Term₀) → State Integer (Constraint Ident Ident Term₀)
desugarF (InL c) = return (Fix c)
desugarF (InR (SEveryF id br)) = do
  br ← desugarBranch br
  return (CEvery id br)
desugarF (InR (SFilterF id filt id')) = do
  filt ← desugarFilter filt
  return (CFilter id filt id')
desugarF (InR (SMatchF tm branches)) = do
    branches ← mapM desugarBranch branches
    return (CMatch tm branches)

desugarPatATm :: ATermF Pattern → DesugarM Term₀
desugarPatATm t = TTm <$> (mapM desugarPattern t)

desugarPatTm :: TermF₀ Pattern → DesugarM Term₀
desugarPatTm t = Fix <$> (mapM desugarPattern t)

desugarPattern :: Pattern → DesugarM Term₀
desugarPattern (PatTm tm) = desugarPatTm tm
desugarPattern Wildcard = do
    x :: Integer ← fresh
    let name = "_" ++ show x
    tell [name]
    return (Var name)

desugarMatcher (Matcher ns pat eqs) = do
  (ns' , pat) ← mapStateT (\wma → fmap (\((tm,s),w) → ((w,tm),s)) (runWriterT wma)) (desugarPattern pat)
  return (Syn.Matcher (ns' ++ ns) pat eqs)
  
desugarBranch (Branch m r) = do
  m ← desugarMatcher m
  return (Syn.Branch m r)

desugarFilter (MatchDatum m) = do
  m ← desugarMatcher m
  return (Syn.MatchDatum m)

