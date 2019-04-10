{-# LANGUAGE ScopedTypeVariables #-}
module Statix.Analysis.Monad where

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
import Statix.Analysis.Typer
import Statix.Analysis.Symboltable
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

instance MonadLex (Ident, TyRef s) IPath (TyRef s) (TCM s) where

  menter c     = local (over scopes (HM.empty:)) c

  mintros xs c = local (over scopes
                        (\sc → (HM.union (head sc) (HM.fromList xs)) : tail sc)) c

  mresolve p   = do
    env ← view scopes
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

instance MonadTyper (TCM s) where
  type World (TCM s) = s
