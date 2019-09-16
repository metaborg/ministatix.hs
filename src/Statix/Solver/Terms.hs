module Statix.Solver.Terms where

import Data.Functor.Fixedpoint
import Control.Monad.State
import Control.Monad.Unique
import Control.Monad.Equiv
import Control.Monad.Writer.Strict

import ATerms.Syntax.ATerm

import Unification as U hiding (TTm)

import Statix.Solver.Types as Solver
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
  n  ← toDag x
  t₂ ← toDag t₂
  l  ← toDag l
  newClass (Rep (SPathCons n l t₂) id)
toDag (PathEnd x) = do
  id ← fresh
  n ← toDag x
  newClass (Rep (SPathEnd n) id)

-- | Convert a solver term to a tree of limited depth.
-- When the maximum depth is reached, terms become wildcards.
instantTerm :: Int → STmRef s → SolverM s String
instantTerm depth n
  | depth >= 1 = do
      t ← getSchema n
      case t of 
        U.Var v → return v
        U.Tm tm → do
          tm ← mapM (instantTerm (depth - 1)) tm
          return $ Solver.pretty id tm
  | otherwise = return "_"

instantVariable d x = do
  t ← lift $ resolve x
  t ← lift $ instantTerm d t
  tell t

instantConstraint :: Int → Constraint₁ → SolverM s String
instantConstraint d c = execWriterT (insta d c)
  where
    insta :: Int → Constraint₁ → WriterT String (SolverM s) ()
    insta d (Ann pos c) = do
      tell $ show pos ++ " | "
      prettyF
        (\qn → tell $ showQName qn)
        (instantVariable d)
        (\t → do
          t ← lift (toDag t)
          t ← lift (instantTerm d t)
          tell t)
        (\ ns c → case ns of
          (Just ns) → tell "_"  -- dont move under binders
          Nothing   → insta d c)
        c
