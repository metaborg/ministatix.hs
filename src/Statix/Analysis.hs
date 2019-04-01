module Statix.Analysis where

import Data.HashMap.Strict as HM
import Control.Monad.State

import Statix.Syntax.Constraint

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Namer
import Statix.Analysis.Typer

-- | Analyze a constraint
analyze :: NameContext → Constraint₀ → TCM Constraint₁
analyze ctx c = do
  liftNC ctx $ checkConstraint c
  -- typecheck qc

-- | Analyze a predicate.
-- This updates the symboltable
analyzeP :: NameContext → Predicate₀ → TCM Predicate₁
analyzeP ctx p = do
  pred ← liftNC ctx $ checkPredicate p

  -- add the predicate to the symbol table
  modify (importP pred)

  -- typecheck it
  -- b' ← typecheck (body pred)

  return pred

-- | Analyze a module
-- (This updates the typechecker symboltable)
analyzeM :: NameContext → Ident → [Predicate₀] → TCM (Module IPath Term₁)
analyzeM ctx mn m = do
  -- name analysis on the module
  mod  ← liftNC ctx $ checkMod mn m

  -- add the module to the symboltable
  modify (importMod mod)

  -- typecheck the module
  -- defs' ← mapM typecheckP (defs mod)
  return $ mod
