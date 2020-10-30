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
import Control.Monad.Equiv

import ATerms.Syntax.Types (Pos(..))

import Statix.Syntax as Syn
import Statix.Analysis.Types
import Statix.Analysis.Lexical as Lex

import Unification as Unif

import Debug.Trace

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
-- checkArity :: MonadTyper n m ⇒ Annotated Pos ConstraintF₁ r → m ()
-- checkArity c@(AnnF pos (CApplyF qn ts)) = do
--   arity ← view (presymtab.arityOf qn)
--   if length ts /= arity
--     then throwError $ WithPosition pos $ ArityMismatch qn arity (length ts)
--     else return ()
-- checkArity c = return ()

initialTable :: MonadTyper n m ⇒ SymbolTable₁ → m (PreSymbolTable n)
initialTable presymtab = forMOf eachFormal presymtab mkBinder

-- | Convert a type node from the unification dag to a ground type
groundType :: MonadTyper n m ⇒ n → m Type
groundType ref = do
  τ ← getSchema ref
  return $ case τ of
    Unif.Tm  ty → getConst ty
    Unif.Var _  → TBot        -- variables indicate we don't know anything

debugType :: MonadTyper n m ⇒ n → m String
debugType ref = do
  τ ← getSchema ref
  return $ case τ of
    Unif.Tm  ty → show $ getConst ty
    Unif.Var n  → "uvar"

-- | Extract a grounded module signature from the typer
solution :: forall n m. MonadTyper n m ⇒ m SymbolTable₂
solution = do
  syms ← view presymtab
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

typeNode :: MonadTyper n m ⇒ Type → m n
typeNode typ = do
  id ← fresh
  newClass (Rep (Tm (Const typ)) id)

-- | Infer types by unification and collect permission constraints.
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
typeAnalysis (CEdge pos n e m)
  | Label l t ← e = do
      n  ← resolve n
      n' ← construct (Tm (Const TNode))
      m  ← resolve m
      m' ← construct (Tm (Const TNode))
      unify n n'
      void $ unify m m'
  | otherwise = throwError $ WithPosition pos $ TypeError "Expected label"
typeAnalysis (CNew _ n t) = do
  n  ← resolve n
  m  ← construct (Tm (Const TNode))
  void $ unify n m
typeAnalysis (CData _ x t) = do
  n  ← resolve x
  m  ← construct (Tm (Const TNode))
  void $ unify n m
typeAnalysis (CQuery _ n r x) = do
  n  ← resolve n
  n' ← construct (Tm (Const TNode))
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
typeAnalysis (CApply pos qn ts) = do
  -- compute the type nodes for the actual parameters
  actuals ← mapM termTypeAnalysis ts

  presyms ← view presymtab
  formals ← case presyms^.lookupPred qn of
    -- apparently a predicate that we are typechecking
    Just pred → do
      -- compute the type nodes for the formal parameters
      return $ fmap snd $ pred^.sig

    -- apparently a predicate that should already be typechecked
    Nothing   → do
      formals ← view (symtab.sigOf qn)
      forM (fmap (^._2) formals) typeNode

  -- arity check
  if length ts /= length formals
    then throwError $ WithPosition pos $ ArityMismatch qn (length formals) (length ts)
    else return ()

  -- check actuals against formals
  catchError
    (void (zipWithM subsumes actuals formals))
    (\case
        UncaughtSubsumptionErr → do
          fms <- mapM debugType formals
          acs <- mapM debugType actuals
          throwError $
            WithPosition pos $
            TypeError $ "Application of " ++ showQName qn ++ " type mismatch"
                      <> "\nexpected: " <> (show fms)
                      <> "\ngot: " <> (show acs)
        e → throwError e
    )

typeAnalysis (CMatch _ t br) = do
  mapM_ typeBranch br

-- | Perform type checking on a constraint in a given module.
-- TODO Think hard about fusion of passses
typecheckConstraint :: (MonadTyper n m) ⇒ Constraint₁ → m ()
typecheckConstraint c = do
  typeAnalysis c

typecheckPredicate :: (MonadTyper n m) ⇒ Predicate₁ → m ()
typecheckPredicate p = do
  bs ← view (presymtab.getPred (p^.qname).sig)
  enters () bs $ do
    void $ typecheckConstraint (p^.body)

typecheckModule :: (MonadTyper n m) ⇒ Module₁ → m ()
typecheckModule mod = forMOf_ (definitions.each) mod typecheckPredicate
