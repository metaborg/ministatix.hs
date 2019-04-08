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

import Statix.Syntax.Constraint
import Statix.Analysis.Types
import Statix.Analysis.Lexical as Lex

import Unification as Unif
import Unification.ST

instance UnificationError TCError where
  symbolClash = TypeError "Type mismatch"
  cyclicTerm  = Panic "Bug" -- should not occur, since types are non-recursive
  
instance MonadEquiv (TyRef s) (TCM s) (Rep (TyRef s) (Const Type) ()) where

  newClass t      = liftST $ newClass t
  repr c          = liftST $ repr c
  description c   = liftST $ description c
  modifyDesc c f  = liftST $ modifyDesc c f
  unionWith c d f = liftST $ Equiv.unionWith c d f

instance ScopedM (TCM s) where
  type Binder (TCM s) = (Ident, TyRef s)
  type Ref    (TCM s) = IPath
  type Datum  (TCM s) = TyRef s

  enter c     = local (HM.empty :) c

  intros xs c = local (\tyenv → (HM.union (head tyenv) (HM.fromList xs)) : tail tyenv) c

  resolve p   = do
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

getPred :: QName → TCM s Predicate₁
getPred q = gets $ view (symtab . to (HM.! q))

unfold :: QName → TCM s Constraint₁
unfold q = body <$> getPred q

-- | Get the signature of a predicate
getSig :: QName → TCM s Signature
getSig q = sig <$> getPred q

-- | Get the arity of a predicate
getArity :: QName → TCM s Int
getArity q = length <$> params <$> getSig q

-- | Check the arity of applications against the symboltable
checkArity :: ConstraintF₁ r → TCM s ()
checkArity c@(CApplyF qn ts) = do
  arity ← getArity qn
  if length ts /= arity
    then throwError $ ArityMismatch qn arity (length ts)
    else return ()
checkArity c = return ()

collectTyConstraints :: Constraint₁ → TCM s ()
collectTyConstraints (CEx ns c) = do
  bs ← mapM mkBinder ns
  enters bs (collectTyConstraints c)
  where
    mkBinder n = do
      v ← freshVar ()
      return (pname n , v)
collectTyConstraints (CEdge n l m)  = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode In)))
  m  ← resolve m
  m' ← construct (Tm (Const (TNode In)))
  unify n n'
  void $ unify m m'
collectTyConstraints (CNew n)       = do
  n  ← resolve n
  m  ← construct (Tm (Const (TNode Out)))
  void $ unify n m
collectTyConstraints (CQuery n r x) = do
  n  ← resolve n
  n' ← construct (Tm (Const (TNode None)))
  unify n n'
  x  ← resolve x
  x' ← construct (Tm (Const TAns))
  void $ unify x x'
collectTyConstraints c = return ()

checker :: Monad m ⇒ a → (a → m ()) → m a
checker a f = do
  f a
  return a

-- | Perform type checking on a constraint against the symboltable
typecheck :: Constraint₁ → TCM s Constraint₁
typecheck c = do
  cataM (checkArity) c
  collectTyConstraints c
  return c
