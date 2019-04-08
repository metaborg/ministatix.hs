{-# LANGUAGE TemplateHaskell #-}
module Statix.Analysis.Types where

import Data.Default
import Data.Text hiding (length, head, tail, find)
import Data.HashMap.Strict as HM
import Data.Coerce
import Data.Functor.Identity
import Data.Maybe
import Data.List

import Control.Lens
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.ST
import Control.Monad.Equiv

import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical
import Unification
import Unification.ST

data TCError
  =
  -- namer errors
    DuplicatePredicate Ident
  | UnboundPredicate Ident
  | UnboundVariable Ident

  -- typer errors
  | ArityMismatch QName Int Int -- pred, expected, got
  | TypeError String

  -- bug!
  | Panic String
  deriving (Show)

-- | Name checking monad
type NCM = ReaderT NameContext (Except TCError)

-- | Type checking monad
type TCM s     = ReaderT (TypeEnv s) (StateT TyState (ExceptT TCError (ST s)))
data TyState   = TyState
  { _symtab :: SymTab
  , _tyid   :: !Int
  }
type TypeEnv s = [Scope s]
type Scope s   = HashMap Ident (TyRef s)
type TyRef s   = Class s (Const Type) ()

data NameContext = NC
  { qualifier :: HashMap Ident QName   -- predicate names → qualified
  , locals    :: [[Ident]]             -- local environment
  }

instance Default NameContext where
  -- Any namecontext should have at least one scope,
  -- the LexicalM interface ensures that the list of active scopes is never empty
  def = NC HM.empty [[]]

instance Default TyState where
  def = TyState HM.empty 0

makeLenses ''TyState

qualify :: Ident → NCM QName
qualify n = do
  mq ← asks (HM.lookup n . qualifier)
  case mq of
    Nothing → throwError (UnboundPredicate n)
    Just q  → return q

runTC :: SymTab → (forall s . TCM s a) → (Either TCError (a , SymTab))
runTC sym c = let result = (runST $ runExceptT (runStateT (runReaderT c []) (set symtab sym def)))
                  in (\(a, st) → (a, view symtab st)) <$> result

runNC :: NameContext → NCM a → Either TCError a
runNC ctx c = runExcept $ runReaderT c ctx

liftST :: ST s a → TCM s a
liftST = lift . lift . lift

liftNC :: NameContext → NCM a → TCM s a
liftNC ctx c = do
  case runNC ctx c of
    Left e  → throwError e
    Right v → return v
