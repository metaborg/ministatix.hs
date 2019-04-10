{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

type PreFormals      s = [ (Ident, TyRef s) ]
type PreModuleTyping s = HashMap Ident (PreFormals s)
type PreSymbolTyping s = HashMap Ident (PreModuleTyping s)

instance UnificationError TCError where
  symbolClash = TypeError "Type mismatch"
  cyclicTerm  = Panic "Bug" -- should not occur, since types are non-recursive
  
instance MonadEquiv (TyRef s) (TCM s) (Rep (TyRef s) (Const Type) ()) where

  newClass t      = liftST $ newClass t
  repr c          = liftST $ repr c
  description c   = liftST $ description c
  modifyDesc c f  = liftST $ modifyDesc c f
  unionWith c d f = liftST $ Equiv.unionWith c d f

type Typing s = (Ident, TyRef s)
instance MonadLex (Typing s) IPath (TyRef s) (TCM s) where
  menter c     = local (HM.empty :) c

  mintros xs c = local (\tyenv → (HM.union (head tyenv) (HM.fromList xs)) : tail tyenv) c

  mresolve p   = do
    env ← ask
    derefLocal p env
    
    where
      derefLocal :: IPath → [Scope s] → TCM s (TyRef s)
      derefLocal (Skip p)     (fr : frs) = derefLocal p frs
      derefLocal (Lex.End id) (fr : frs) =
        case HM.lookup id fr of
          Nothing → throwError $ Panic "Unbound variable during typechecking"
          Just t  → return t
      derefLocal _ _                    =
        throwError $ Panic "Unbound variable during typechecking"

instance MonadUnique Int (TCM s) where
  fresh = do
    id ← gets (view tyid)
    tyid %= (+1) 
    return id

instance MonadUnify (Const Type) (TyRef s) () TCError (TCM s) where

-- | Abstract typer monad class as a composition of various other monads.
class (
    MonadLex (Typing (World m)) IPath (TyRef (World m)) m
  , MonadUnify (Const Type) (TyRef (World m)) () TCError m
  , MonadUnique Int m
  , MonadError TCError m
  , MonadState SymbolTyping m
  , MonadReader (Ident, PreModuleTyping (World m)) m) ⇒ MonadTyper m where
  type World m :: *

getFormals :: (MonadState SymbolTyping m) ⇒ QName → m Formals
getFormals (mod, name) = gets ((HM.! name) . (HM.! mod))

-- | Get the arity of a predicate
getArity :: (MonadState SymbolTyping m) ⇒ QName → m Int
getArity q = length <$> getFormals q

-- | Check the arity of applications against the symboltable
checkArity :: (MonadError TCError m, MonadState SymbolTyping m) ⇒ ConstraintF₁ r → m ()
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return ()
checkArity c = return ()

termTypeAnalysis :: MonadTyper m ⇒ Term₁ → m (TyRef (World m))
termTypeAnalysis (Term.Var x) = mresolve x
termTypeAnalysis (Label _)    = construct (Tm (Const TLabel))
termTypeAnalysis (Path _ _ _) = construct (Tm (Const TPath))
termTypeAnalysis _            = construct (Tm (Const TBot))

-- | Analyze existential variable and parameter types
typeAnalysis :: MonadTyper m ⇒ Constraint₁ → m ()
typeAnalysis CTrue  = return ()
typeAnalysis CFalse = return ()
typeAnalysis (CEx ns c) = do
  bs ← mapM mkBinder ns
  menters bs (typeAnalysis c)
  where
    mkBinder n = do
      v ← freshVar ()
      return (pname n , v)
typeAnalysis (CAnd c d) = do
  typeAnalysis c
  typeAnalysis d
typeAnalysis (CEdge n l m)  = do
  n  ← mresolve n
  n' ← construct (Tm (Const (TNode In)))
  m  ← mresolve m
  m' ← construct (Tm (Const (TNode In)))
  unify n n'
  void $ unify m m'
typeAnalysis (CNew n)       = do
  n  ← mresolve n
  m  ← construct (Tm (Const (TNode Out)))
  void $ unify n m
typeAnalysis (CQuery n r x) = do
  n  ← mresolve n
  n' ← construct (Tm (Const (TNode None)))
  unify n n'
  x  ← mresolve x
  x' ← construct (Tm (Const TAns))
  void $ unify x x'
typeAnalysis (CEvery x y c) = do
  y  ← mresolve y
  y' ← construct (Tm (Const TAns))
  unify y y'
  typeAnalysis c
typeAnalysis (COne x t) = do
  x  ← mresolve x
  x' ← construct (Tm (Const TAns))
  unify x x'
typeAnalysis (CApply (mod, name) ts) = do
  self ← asks fst

  -- compute the type nodes for the formal parameters 
  actuals ← mapM termTypeAnalysis ts

  -- get the formal parameter types
  formals ← if (mod == self)
    then do
      -- get the type nodes for the formal parameters from the module pretyping
      binders ← asks ((HM.! name) . snd)
      return (snd <$> binders)

    else do
      -- get the type nodes for the formal parameters from the symboltable
      -- and convert to dag
      binders ← gets ((HM.! name) . (HM.! mod))
      mapM (\(_, σ) → construct (Tm $ Const σ)) binders

  -- unify formals with actuals
  void (zipWithM unify formals actuals)
  
-- | Perform type checking on a constraint in a given module.
-- 
typecheck :: (MonadTyper m) ⇒ Constraint₁ → m Constraint₁
typecheck c = do
  -- we run some checks on the constranit that do not
  -- require additional type annotations
  cataM checkArity c

  -- constraint based type analysis
  typeAnalysis c

  -- for now we just return the inputted constraint
  return c
