module Statix.Analysis where

import Data.HashMap.Strict as HM
import Control.Monad.State

import Statix.Syntax.Constraint

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Namer
import Statix.Analysis.Typer

analyze :: Context → Constraint RawName n → TCM (Constraint QName n)
analyze ctx c = do
  qc ← liftNC ctx $ checkConstraint c
  typecheck qc

analyzeP :: Context → Predicate RawName → TCM (Predicate QName)
analyzeP ctx p = do
  pred ← liftNC ctx $ checkPredicate p

  -- add the predicate to the symbol table
  modify (importP pred)

  -- typecheck it
  b' ← typecheck (body pred)

  return $ pred { body = b' }

analyzeM :: Context → ModName → [Predicate RawName] → TCM Module
analyzeM ctx mn m = do
  -- name analysis on the module
  mod  ← checkMod mn m

  -- add the module to the symboltable
  modify (importMod mod)

  -- typecheck the module
  defs' ← mapM typecheckP (defs mod)
  return $ mod { defs = defs' }
