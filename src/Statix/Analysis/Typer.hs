{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Type checking internals.
--
-- Using these functions requires careful preparation of the type environment
-- and state in the monad.
--
-- Use the Statix.Analysis frontend to the typer if possible instead.
module Statix.Analysis.Typer where

import Data.Functor.Fixedpoint
import Data.Default
import Data.HashMap.Strict as HM
import Data.Set as S

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
  ( MonadLex (Ident, n) IPath n m
  , MonadUnify (Const Type) n () TCError m
  , MonadUnique Integer m
  , MonadError TCError m
  , MonadReader (TyEnv n) m
  ) ⇒ MonadTyper n m | m → n where

getFormals :: MonadTyper n m ⇒ QName → m (PreFormals n)
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
      binders ← view (symty . to (!!! qn) . to sig)
      mapM (\(name, σ) → do n ← construct (Tm $ Const σ); return (name , n)) binders

-- | Get the arity of a predicate
getArity :: MonadTyper n m ⇒ QName → m Int
getArity q = length <$> getFormals q

-- | Check the arity of applications against the symboltable
checkArity :: MonadTyper n m ⇒ ConstraintF₁ r → m ()
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return ()
checkArity c = return ()

predInitialTyping ::
  ( MonadUnique Integer m
  , MonadEquiv n m (Rep n (Const Type) ())
  ) ⇒ Predicate₁ → m (PreFormals n)
predInitialTyping p = do
  let (_, name) = qname p
  let formals   = sig p
  -- for every formal parameter
  forM formals $ \(n,_) → do
    v ← freshVar ()
    return (n, v)

modInitialTyping ::
  ( MonadUnique Integer m
  , MonadEquiv n m (Rep n (Const Type) ())
  ) ⇒ Module → m (PreModuleTyping n)
modInitialTyping mod = forM mod predInitialTyping

-- | Convert a type node from the unification dag to a ground type
groundType :: MonadTyper n m ⇒ n → m Type
groundType ref = do
  τ ← getSchema ref
  return $ case τ of
    Unif.Tm  ty → getConst ty
    Unif.Var _  → TBot        -- variables indicate we don't know anything

-- | Extract a grounded module signature from the typer
solution :: MonadTyper n m ⇒ m ModuleSig
solution = do
  pretype ← view modtable
  forM pretype $ \formals → do
    forM formals $ \(param, tyref) → do
      τ ← groundType tyref
      return (param, τ)

termTypeAnalysis :: MonadTyper n m ⇒ Term₁ → m n
termTypeAnalysis (Term.Var x) = resolve x
termTypeAnalysis (Label _ _)  = construct (Tm (Const TLabel))
termTypeAnalysis (PathCons _ _ _) = construct (Tm (Const TPath))
termTypeAnalysis (PathEnd _)  = construct (Tm (Const TPath))
termTypeAnalysis _            = construct (Tm (Const TBot))

mkBinder :: MonadTyper n m ⇒ Ident → m (Ident, n)
mkBinder n = do
 v ← freshVar ()
 return (n , v)

typeMatch  :: MonadTyper n m ⇒ Matcher Term₁ → m a → m a
typeMatch (Matcher ps t eqs) ma = do
  bs ← mapM mkBinder ps
  enters bs ma

typeBranch :: MonadTyper n m ⇒ Branch₁ → m ()
typeBranch (Branch m c) = do
  typeMatch m (typeAnalysis c)

-- | Collect type constraints
typeAnalysis :: MonadTyper n m ⇒ Constraint₁ → m ()
typeAnalysis CTrue  = return ()
typeAnalysis CFalse = return ()
typeAnalysis (CEx ns c) = do
  bs ← mapM mkBinder ns
  enters bs (typeAnalysis c)
typeAnalysis (CAnd c d) = do
  typeAnalysis c
  typeAnalysis d
typeAnalysis (CEq t s) =
  return ()
typeAnalysis (CEdge n e m)
  | Label l t ← e = do
      n  ← resolve n
      n' ← construct (Tm (Const (TNode (In (S.singleton l)))))
      m  ← resolve m
      m' ← construct (Tm (Const (TNode None)))
      unify n n'
      void $ unify m m'
  | otherwise = throwError $ TypeError "Expected label"
typeAnalysis (CNew n)       = do
  n  ← resolve n
  m  ← construct (Tm (Const (TNode Out)))
  void $ unify n m
typeAnalysis (CData x t)       = do
  n  ← resolve x
  m  ← construct (Tm (Const (TNode None)))
  void $ unify n m
typeAnalysis (CQuery n r x) = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode None)))
  unify n n'
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  void $ unify x x'
typeAnalysis (CEvery x br) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
  typeBranch br 
typeAnalysis (COne x t) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
typeAnalysis (CMin x p y) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  y  ← resolve y
  y' ← construct (Tm (Const TAns))
  unify x x'
  unify y y'
typeAnalysis (CFilter x p y) = do
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  y  ← resolve y
  y' ← construct (Tm (Const TAns))
  unify x x'
  unify y y'
typeAnalysis (CApply qn ts) = do
  -- compute the type nodes for the formal parameters 
  formals ← getFormals qn
  actuals ← mapM termTypeAnalysis ts

  -- unify formals with actuals
  void (zipWithM unify (fmap snd formals) actuals)
typeAnalysis (CMatch t br) = do
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
  bs ← getFormals (qname p)
  enters bs $ do
    void $ typecheckConstraint (body p)
