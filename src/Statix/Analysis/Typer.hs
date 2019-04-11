{-# LANGUAGE AllowAmbiguousTypes #-}
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

modInitialTyping :: (MonadTyper m) ⇒ Module → m (PreModuleTyping (World m))
modInitialTyping mod = do
  -- for every predicate in the module
  forM mod $ \ p → do
    let (_, name) = qname p
    let formals   = sig p
    -- for every formal parameter
    forM formals $ \(n,_) → do
      v ← freshVar ()
      return (n, v)

-- | Convert a type node from the unification dag to a ground type
groundType :: MonadTyper m ⇒ TyRef (World m) → m Type
groundType ref = do
  τ ← getSchema ref
  return $ case τ of
    Unif.Tm  ty → getConst ty
    Unif.Var _  → TBot        -- variables indicate we don't know anything

-- | Extract a grounded module signature from the typer
solution :: MonadTyper m ⇒ m ModuleSig
solution = do
  pretype ← view modtable
  forM pretype $ \formals → do
    forM formals $ \(param, tyref) → do
      τ ← groundType tyref
      return (param, τ)

termTypeAnalysis :: MonadTyper m ⇒ Term₁ → m (TyRef (World m))
termTypeAnalysis (Term.Var x) = resolve x
termTypeAnalysis (Label _)    = construct (Tm (Const TLabel))
termTypeAnalysis (Path _ _ _) = construct (Tm (Const TPath))
termTypeAnalysis _            = construct (Tm (Const TBot))

mkBinder :: MonadTyper m ⇒ Ident → m (Ident, TyRef (World m))
mkBinder n = do
 v ← freshVar ()
 return (n , v)

-- | Analyze existential variable and parameter types
typeAnalysis :: MonadTyper m ⇒ Constraint₁ → m ()
typeAnalysis CTrue  = return ()
typeAnalysis CFalse = return ()
typeAnalysis (CEx ns c) = do
  bs ← mapM mkBinder ns
  enters bs (typeAnalysis c)
  where
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
typecheck :: (MonadTyper m) ⇒ Constraint₁ → m ()
typecheck c = do
  -- we run some checks on the constranit that do not
  -- require additional type annotations
  cataM checkArity c

  -- constraint based type analysis
  typeAnalysis c

typecheckPredicate :: (MonadTyper m) ⇒ Predicate₁ → m ()
typecheckPredicate p = do
  let ns = fmap fst (sig p)
  bs ← mapM mkBinder ns
  enters bs $ do
    void $ typecheck (body p)

typecheckModule :: (MonadTyper m) ⇒ Ident → Module → m Module
typecheckModule this mod = do
  -- initiate the module typing
  pretype ← modInitialTyping mod

  -- compute the module signature
  sig ← local (set self this . set modtable pretype) $ do
    forM mod typecheckPredicate
    solution

  -- annotate the module with the computed signature
  case annotateModule sig mod of
    Just annotated → return annotated
    Nothing        → throwError $ Panic "Module signature incomplete"
