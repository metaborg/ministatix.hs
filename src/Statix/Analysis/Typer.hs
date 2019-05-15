{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Type checking internals.
--
-- Using these functions requires careful preparation of the type environment
-- and state in the monad.
--
-- Use the Statix.Analysis frontend to the typer if possible instead.
module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint
import Data.Set as S

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Unique

import Statix.Syntax as Syn
import Statix.Analysis.Types
import Statix.Analysis.Lexical as Lex

import Unification as Unif

-- | Abstract typer monad class as a composition of various other monads.
class
  ( MonadLex (Ident, n) IPath n m
  , MonadUnify (Const Type) n () TCError m
  , MonadUnique Integer m
  , MonadError TCError m
  , MonadReader (TyEnv n) m
  , FrameDesc m ~ ()
  ) ⇒ MonadTyper n m | m → n where

-- | Check the arity of applications against the symboltable
checkArity :: MonadTyper n m ⇒ Annotated Pos ConstraintF₁ r → m ()
checkArity c@(AnnF _ (CApplyF qn ts)) = do
  arity ← view (symtab.arityOf qn)
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return ()
checkArity c = return ()

initialTable :: MonadTyper n m ⇒ SymbolTable₁ → m (PreSymbolTable n)
initialTable symtab = forMOf eachFormal symtab mkBinder 

-- | Convert a type node from the unification dag to a ground type
groundType :: MonadTyper n m ⇒ n → m Type
groundType ref = do
  τ ← getSchema ref
  return $ case τ of
    Unif.Tm  ty → getConst ty
    Unif.Var _  → TBot        -- variables indicate we don't know anything

-- | Extract a grounded module signature from the typer
solution :: forall n m. MonadTyper n m ⇒ m SymbolTable₂
solution = do
  syms ← view symtab
  mapMOf (eachFormal._2) groundType syms

termTypeAnalysis :: MonadTyper n m ⇒ Term₁ → m n
termTypeAnalysis (Syn.Var x)      = resolve x
termTypeAnalysis (Label _ _)      = construct (Tm (Const TLabel))
termTypeAnalysis (PathCons _ _ _) = construct (Tm (Const TPath))
termTypeAnalysis (PathEnd _)      = construct (Tm (Const TPath))
termTypeAnalysis _                = construct (Tm (Const TBot))

mkBinder :: MonadTyper n m ⇒ Ident → m (Ident, n)
mkBinder n = do
 v ← freshVar ()
 return (n , v)

typeMatch  :: MonadTyper n m ⇒ Matcher Term₁ → m a → m a
typeMatch (Matcher ps t eqs) ma = do
  bs ← mapM mkBinder ps
  enters () bs ma

typeBranch :: MonadTyper n m ⇒ Branch₁ → m ()
typeBranch (Branch m c) = do
  typeMatch m (typeAnalysis c)

-- | Collect type constraints
typeAnalysis :: MonadTyper n m ⇒ Constraint₁ → m ()
typeAnalysis (CTrue _)  = return ()
typeAnalysis (CFalse _) = return ()
typeAnalysis (CEx _ ns c) = do
  bs ← mapM mkBinder ns
  enters () bs (typeAnalysis c)
typeAnalysis (CAnd _ c d) = do
  typeAnalysis c
  typeAnalysis d
typeAnalysis (CEq _ t s) =
  return ()
typeAnalysis (CNotEq _ t s) =
  return ()
typeAnalysis (CEdge _ n e m)
  | Label l t ← e = do
      n  ← resolve n
      n' ← construct (Tm (Const (TNode (In (S.singleton l)))))
      m  ← resolve m
      m' ← construct (Tm (Const (TNode None)))
      unify n n'
      void $ unify m m'
  | otherwise = throwError $ TypeError "Expected label"
typeAnalysis (CNew _ n t) = do
  n  ← resolve n
  m  ← construct (Tm (Const (TNode Out)))
  void $ unify n m
typeAnalysis (CData _ x t) = do
  n  ← resolve x
  m  ← construct (Tm (Const (TNode None)))
  void $ unify n m
typeAnalysis (CQuery _ n r x) = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode None)))
  unify n n'
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  void $ unify x x'
typeAnalysis (CEvery _ x br) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
  typeBranch br 
typeAnalysis (COne _ x t) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
typeAnalysis (CNonEmpty _ x) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
typeAnalysis (CMin _ x p y) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  y  ← resolve y
  y' ← construct (Tm (Const TAns))
  unify x x'
  unify y y'
typeAnalysis (CFilter _ x p y) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  y  ← resolve y
  y' ← construct (Tm (Const TAns))
  unify x x'
  unify y y'
typeAnalysis (CApply _ qn ts) = do
  -- compute the type nodes for the formal parameters 
  formals ← view $ symtab . sigOf qn
  actuals ← mapM termTypeAnalysis ts

  -- unify formals with actuals
  void (zipWithM unify (fmap snd formals) actuals)
typeAnalysis (CMatch _ t br) = do
  mapM_ typeBranch br
  
-- | Perform type checking on a constraint in a given module.
-- TODO Think hard about fusion of passses
typecheckConstraint :: (MonadTyper n m) ⇒ Constraint₁ → m ()
typecheckConstraint c = do
  -- we run some checks on the constranit that do not
  -- require additional type annotations
  cataM checkArity c

  -- constraint based type analysis
  typeAnalysis c

typecheckPredicate :: (MonadTyper n m) ⇒ Predicate₁ → m ()
typecheckPredicate p = do
  bs ← view (symtab.getPred (p^.qname).sig)
  enters () bs $ do
    void $ typecheckConstraint (p^.body)

typecheckModule :: (MonadTyper n m) ⇒ Module₁ → m ()
typecheckModule mod = forMOf_ (definitions.each) mod typecheckPredicate
