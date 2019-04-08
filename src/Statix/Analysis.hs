module Statix.Analysis where

import Data.HashMap.Strict as HM

import Control.Monad.State
import Control.Lens

import Statix.Syntax.Constraint

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Namer
import Statix.Analysis.Typer

-- | Analyze a constraint
analyze :: NameContext → Constraint₀ → TCM s Constraint₁
analyze ctx c = do
  c ← liftNC ctx $ checkConstraint c
  typecheck c

-- | Analyze a predicate.
analyzeP :: NameContext → Predicate₀ → TCM s Predicate₁
analyzeP ctx p = do
  pred ← liftNC ctx $ checkPredicate p

  -- Add the predicate to the symbol table.
  -- This is fine, because we won't return the updated table if checking fails
  symtab %= importP pred

  -- typecheck it
  typecheck (body pred)

  return pred

-- | Analyze a module
-- (This updates the typechecker symboltable)
analyzeM :: NameContext → Ident → [Predicate₀] → TCM s (Module IPath Term₁)
analyzeM ctx mn m = do
  -- name analysis on the module
  mod  ← liftNC ctx $ checkMod mn m

  -- add the module to the symboltable
  symtab %= importMod mod

  -- typecheck the module
  -- defs' ← mapM typecheckP (defs mod)
  return $ mod
