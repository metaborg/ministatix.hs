{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
module Statix.Solver.Terms where

import Data.Text (Text, pack)
import Data.Functor.Fixedpoint
import Control.Monad.State
import Control.Monad.Unique
import Control.Monad.Equiv
import Control.Monad.Writer.Strict

import ATerms.Syntax.ATerm

import Unification as U hiding (TTm)

import Statix.Solver.Types
import Statix.Solver.Monad
import Statix.Analysis.Lexical
import Statix.Syntax as Syn
import Statix.Syntax.Pretty

-- | Embedding of syntactical terms into the DAG representation of terms
toDag :: Term₁ → SolverM s (STmRef s)
toDag (Syn.Var p)    =
  resolve p
toDag (TTm t) = do
  id ← fresh
  t ← mapM toDag t
  newClass (Rep (STm t) id)
toDag (Label l t) = do
  id ← fresh
  t ← mapM toDag t
  newClass (Rep (SLabel l t) id)
toDag (PathCons x l t₂) = do
  id ← fresh
  n  ← resolve x
  t₂ ← toDag t₂
  l  ← toDag l
  newClass (Rep (SPathCons n l t₂) id)
toDag (PathEnd x) = do
  id ← fresh
  n ← resolve x
  newClass (Rep (SPathEnd n) id)

hole :: STree s
hole = Fix (Tm (STmF AWildCardF))

-- | Convert a solver term to a tree of limited depth.
-- When the maximum depth is reached, terms become wildcards.
delimitedTree :: Int → STmRef s → SolverM s (STree s)
delimitedTree depth n
  | depth >= 1 = do
      t ← getSchema n
      case t of 
        U.Var v → return (Fix (U.Var v))
        U.Tm tm  → do
          subtree ← mapM (delimitedTree (depth - 1)) tm
          return (Fix (Tm subtree))
  | otherwise = return hole

instantConstraint :: Int → Constraint₁ → SolverM s Text
instantConstraint d c = execWriterT (insta d c)
  where
    insta :: Int → Constraint₁ → WriterT Text (SolverM s) ()
    insta d (Fix c) = prettyF
      (\qn → tell $ pack $ showQName qn)
      (\x  → do
          t ← lift $ resolve x
          t ← lift $ delimitedTree d t
          tell $ pack $ show t)
      (\t → do
          t ← lift (toDag t)
          t ← lift $ delimitedTree d t
          tell $ pack $ show t)
      (\ ns c → case ns of
        (Just ns) → tell "_"  -- dont move under binders
        Nothing   → insta d c)
      c
