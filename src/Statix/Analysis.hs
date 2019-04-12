module Statix.Analysis where

import Data.HashMap.Strict as HM
import Data.Default

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Unique
import Control.Lens

import Statix.Syntax.Constraint

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Types.ST
import Statix.Analysis.Namer
import Statix.Analysis.Namer.Simple

typecheck :: Ident → [Predicate₀] → SymbolTable → Module
typecheck modulename mod symab = _
  do
  -- initiate the module typing
  pretype ← modInitialTyping mod

  let tyenv = TyEnv
        { _self = this
        , _modtable pretype
        , _symty = symtab
                    }
  -- compute the module signature
  sig ← local tyenv $ do
    forM mod typecheckPredicate
    solution

  -- annotate the module with the computed signature
  case annotateModule sig mod of
    Just annotated → return annotated
    Nothing        → throwError $ Panic "Module signature incomplete"

-- class (Monad m, MonadTyper (Typer m), MonadNamer (Namer m)) ⇒ MonadAnalysis m where
--   type Typer m :: * → *
--   type Namer m :: * → *

--   namer   :: Namer m a → m a
--   typer   :: Typer m a → m a

--   imports :: Predicate₁ → m ()

-- importsMod :: MonadAnalysis m ⇒ Module → m ()
-- importsMod mod = mapM_ imports mod

-- -- | Analyze a constraint
-- analyze :: (MonadAnalysis m) ⇒ Constraint₀ → m Constraint₁
-- analyze c = do
--   c ← namer $ checkConstraint c
--   typer $ typecheck c
--   return c

-- -- | Analyze a predicate
-- analyzePred :: (MonadAnalysis m) ⇒ Predicate₀ → m Predicate₁
-- analyzePred p = do
--   pred ← namer $ checkPredicate p
--   typer $ typecheckPredicate pred
--   return pred

-- analyzeModule :: (MonadAnalysis m) ⇒ Ident → [Predicate₀] → m Module
-- analyzeModule modname rawmod = do
--   mod ← namer $ checkMod modname rawmod
--   typer $ typecheckModule modname mod
