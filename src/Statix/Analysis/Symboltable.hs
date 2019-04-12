module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM

import Control.Lens
import Control.Monad

import Statix.Syntax.Constraint

type Module       = HashMap Ident Predicate₁
type ModuleSig    = HashMap Ident Signature

type SymbolTable  = HashMap Ident Module

-- | Annotate a module with a signature.
-- Fails if the module signature misses entries
annotateModule :: ModuleSig → Module → Maybe Module
annotateModule σ m =
  forM m (annotate σ)

  where
    annotate :: ModuleSig → Predicate₁ → Maybe Predicate₁
    annotate σ p = do
      sig ← HM.lookup (snd $ qname p) σ
      return $ p { sig = sig }
