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
type TCM s     =
  ( ReaderT (TyEnv s)
  ( StateT Int
  ( ExceptT TCError
  ( ST s ))))

type Scope s   = HashMap Ident (TyRef s)
type TyRef s   = Class s (Const Type) ()

type PreFormals      s = [ (Ident, TyRef s) ]
type PreModuleTyping s = HashMap Ident (PreFormals s)

data TyEnv s = TyEnv
  { _self     :: Ident
  , _modtable :: PreModuleTyping s
  , _symty    :: SymbolTable
  , _scopes   :: [Scope s]
  }

data NameContext = NC
  { _qualifier :: Qualifier -- predicate names → qualified
  , _locals    :: [[Ident]] -- local environment
  }
type Qualifier = HashMap Ident QName
 
instance Default (TyEnv s) where
  def = TyEnv (pack "") HM.empty HM.empty [HM.empty]

instance Default NameContext where
  -- Any namecontext should have at least one scope,
  -- the LexicalM interface ensures that the list of active scopes is never empty
  def = NC HM.empty [[]]
 
makeLenses ''TyEnv
makeLenses ''NameContext

runTC :: TyEnv s → Int → TCM s a → ST s (Either TCError (a, Int))
runTC env i c = do
  runExceptT $ runStateT (runReaderT c env) i

runNC :: NameContext → NCM a → Either TCError a
runNC ctx c = runExcept $ runReaderT c ctx

liftST :: ST s a → TCM s a
liftST = lift . lift . lift

liftNC :: NameContext → NCM a → TCM s a
liftNC ctx c = do
  case runNC ctx c of
    Left e  → throwError e
    Right v → return v
