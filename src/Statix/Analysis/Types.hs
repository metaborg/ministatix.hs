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

instance HasClashError (Const Type) TCError where
  symbolClash l r = TypeError $ "Type mismatch: " ++ show l ++ " != " ++ show r

instance HasCyclicError TCError where
  cyclicTerm      = Panic "Bug" -- should not occur, since types are non-recursive

data NameContext = NC
  { _qualifier :: Qualifier -- predicate names → qualified
  , _locals    :: [[Ident]] -- local environment
  }
type Qualifier = HashMap Ident QName

instance Default NameContext where
  -- Any namecontext should have at least one scope,
  -- the LexicalM interface ensures that the list of active scopes is never empty
  def = NC HM.empty [[]]
 
makeLenses ''NameContext

type Scope n           = HashMap Ident n
type PreFormals n      = [ (Ident, n) ]
type PreModuleTyping n = HashMap Ident (PreFormals n)
type TyRef s           = Class s (Const Type) ()

data TyEnv n = TyEnv
  { _self     :: Ident
  , _modtable :: PreModuleTyping n
  , _symty    :: SymbolTable
  , _scopes   :: [Scope n]
  }

instance Default (TyEnv n) where
  def = TyEnv (pack "") HM.empty HM.empty [HM.empty]

makeLenses ''TyEnv
