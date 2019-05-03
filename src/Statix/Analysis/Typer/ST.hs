module Statix.Analysis.Typer.ST where

import Data.Default
import Data.HashMap.Strict as HM
import qualified Data.Text as Text

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Equiv as Equiv
import Control.Monad.State
import Control.Monad.Unique
import Control.Monad.ST

import Statix.Syntax.Constraint as Term
import Statix.Analysis.Types
import Statix.Analysis.Typer
import Statix.Analysis.Namer
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical as Lex


import Unification as Unif
import Unification.ST

-- | Type checking monad
type TCM s =
  ( ReaderT (TyEnv (TyRef s))
  ( StateT Integer
  ( ExceptT TCError
  ( ST s ))))

runTC :: TyEnv (TyRef s) → Integer → TCM s a → ST s (Either TCError (a, Integer))
runTC env i c = do
  runExceptT $ runStateT (runReaderT c env) i

liftST :: ST s a → TCM s a
liftST = lift . lift . lift

instance MonadEquiv (TyRef s) (TCM s) (Rep (TyRef s) (Const Type) ()) where
  newClass t      = liftST $ newClass t
  repr c          = liftST $ repr c
  description c   = liftST $ description c
  modifyDesc c f  = liftST $ modifyDesc c f
  unionWith c d f = liftST $ Equiv.unionWith c d f

instance MonadUnique Integer (TCM s) where
  fresh      = lift fresh
  updateSeed = lift . updateSeed

instance MonadLex (Ident, TyRef s) IPath (TyRef s) (TCM s) where
  type FrameDesc (TCM s) = ()

  enter _ = local (over scopes (HM.empty:))

  intros xs =
    local (over scopes (\sc → (HM.union (head sc) (HM.fromList xs)) : tail sc))

  resolve p   = do
    env ← view scopes
    derefLocal p env
    
    where
      derefLocal :: IPath → [Scope (TyRef s)] → TCM s (TyRef s)
      derefLocal (Skip p)     (fr : frs) = derefLocal p frs
      derefLocal (Lex.End id) (fr : frs) =
        case HM.lookup id fr of
          Nothing → throwError $ Panic "Unbound variable during typechecking"
          Just t  → return t
      derefLocal _ _                    =
        throwError $ Panic "Unbound variable during typechecking"

instance MonadUnify (Const Type) (TyRef s) () TCError (TCM s) where

instance MonadTyper (TyRef s) (TCM s) where
