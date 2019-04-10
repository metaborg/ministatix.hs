{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint
import Data.Default
import Data.HashMap.Strict as HM

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Equiv as Equiv
import Control.Monad.State
import Control.Monad.Unique
import Control.Applicative

import Statix.Syntax.Constraint as Term
import Statix.Analysis.Types
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical as Lex

import Unification as Unif
import Unification.ST

-- | Abstract typer monad class as a composition of various other monads.
class
  ( MonadLex (Ident, TyRef (World m)) IPath (TyRef (World m)) m
  , MonadUnify (Const Type) (TyRef (World m)) () TCError m
  , MonadUnique Int m
  , MonadError TCError m
  , MonadReader (TyEnv (World m)) m
  ) ⇒ MonadTyper m where
  type World m :: *

getFormals :: MonadTyper m ⇒ QName → m (PreFormals (World m))
getFormals qn@(mod, name) = do
  self ← view self
  if (mod == self)
    then do
      -- get the type nodes for the formal parameters from the module pretyping
      binders ← view (modtable . to (HM.! name))
      return binders

    else do
      -- get the type nodes for the formal parameters from the symboltable
      -- and convert to dag
      binders ← view (symty . to (HM.! qn) . to sig)
      mapM (\(name, σ) → do n ← construct (Tm $ Const σ); return (name , n)) binders

-- | Get the arity of a predicate
getArity :: MonadTyper m ⇒ QName → m Int
getArity q = length <$> getFormals q

-- | Check the arity of applications against the symboltable
checkArity :: MonadTyper m ⇒ ConstraintF₁ r → m ()
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return ()
checkArity c = return ()

termTypeAnalysis :: MonadTyper m ⇒ Term₁ → m (TyRef (World m))
termTypeAnalysis (Term.Var x) = resolve x
termTypeAnalysis (Label _)    = construct (Tm (Const TLabel))
termTypeAnalysis (Path _ _ _) = construct (Tm (Const TPath))
termTypeAnalysis _            = construct (Tm (Const TBot))

-- | Analyze existential variable and parameter types
typeAnalysis :: MonadTyper m ⇒ Constraint₁ → m ()
typeAnalysis CTrue  = return ()
typeAnalysis CFalse = return ()
typeAnalysis (CEx ns c) = do
  bs ← mapM mkBinder ns
  enters bs (typeAnalysis c)
  where
    mkBinder n = do
      v ← freshVar ()
      return (n , v)
typeAnalysis (CAnd c d) = do
  typeAnalysis c
  typeAnalysis d
typeAnalysis (CEq t s) = do
  τ ← termTypeAnalysis t
  σ ← termTypeAnalysis s
  unify τ σ
typeAnalysis (CEdge n l m)  = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode In)))
  m  ← resolve m
  m' ← construct (Tm (Const (TNode In)))
  unify n n'
  void $ unify m m'
typeAnalysis (CNew n)       = do
  n  ← resolve n
  m  ← construct (Tm (Const (TNode Out)))
  void $ unify n m
typeAnalysis (CQuery n r x) = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode None)))
  unify n n'
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  void $ unify x x'
typeAnalysis (CEvery x y c) = do
  y  ← resolve y
  y' ← construct (Tm (Const TAns))
  unify y y'
  typeAnalysis c
typeAnalysis (COne x t) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
typeAnalysis (CApply qn ts) = do
  -- compute the type nodes for the formal parameters 
  formals ← getFormals qn
  actuals ← mapM termTypeAnalysis ts

  -- unify formals with actuals
  void (zipWithM unify (fmap snd formals) actuals)
  
-- | Perform type checking on a constraint in a given module.
-- TODO Think hard about fusion of passses
typecheck :: (MonadTyper m) ⇒ Constraint₁ → m Constraint₁
typecheck c = do
  -- we run some checks on the constranit that do not
  -- require additional type annotations
  cataM checkArity c

  -- constraint based type analysis
  typeAnalysis c

  -- for now we just return the inputted constraint
  return c
