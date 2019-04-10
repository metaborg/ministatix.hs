module Statix.Analysis where

import Data.HashMap.Strict as HM
import Data.Default

import Control.Monad.State
import Control.Monad.Reader
import Control.Lens

import Statix.Syntax.Constraint

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Namer
import Statix.Analysis.Typer
import Statix.Analysis.Monad

class (Monad m, MonadTyper (Typer m), MonadNamer (Namer m)) ⇒ MonadAnalysis m where
  type Typer m :: * → *
  type Namer m :: * → *

  namer   :: Namer m a → m a
  typer   :: Typer m a → m a

  imports :: Predicate₁ → m ()

importsMod :: MonadAnalysis m ⇒ Module → m ()
importsMod mod = mapM_ imports mod

-- | Analyze a constraint
analyze :: (MonadAnalysis m) ⇒ Constraint₀ → m Constraint₁
analyze c = do
  c ← namer $ checkConstraint c
  typer $ typecheck c

-- | Analyze a predicate
analyzePred :: (MonadAnalysis m) ⇒ Predicate₀ → m Predicate₁
analyzePred p = do
  pred ← namer $ checkPredicate p

  typer $ typecheck (body pred)

  return pred
