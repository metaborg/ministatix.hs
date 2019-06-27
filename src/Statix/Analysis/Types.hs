module Statix.Analysis.Types where

import Data.Default
import Data.Set
import Data.HashMap.Strict as HM hiding (map)
import Control.Lens

import Statix.Syntax

import Unification
import Unification.ST

data TCError
  =
  ModuleLocal String TCError
  | WithPosition Pos TCError
  | WithPredicate QName TCError
  
  -- namer errors
  | DuplicatePredicate Ident
  | UnboundPredicate Ident
  | UnboundVariable Ident
  | MatchCaptures Ident

  -- typer errors
  | ArityMismatch QName Int Int -- pred, expected, got
  | PermissionError Ident (Set Label)
  | TypeError String

  -- bug!
  | UncaughtSubsumptionErr
  | Panic String
  deriving (Show)

instance HasClashError (Const Type) TCError where
  symbolClash l r = TypeError $ "Type mismatch: " ++ show l ++ " != " ++ show r

instance HasCyclicError TCError where
  cyclicTerm      = Panic "Bug" -- should not occur, since types are non-recursive

instance HasSubsumptionError TCError where
  doesNotSubsume  = UncaughtSubsumptionErr

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

type PreSignature n    = [ (Ident, n) ]
type PrePredicate n    = Predicate (Ident, n) Constraint₁
type PreModule n       = Module Ident Constraint₁
type PreSymbolTable n  = SymbolTable (Ident, n) Constraint₁

type TyRef s           = Class s (Const Type) ()

data TyEnv n = TyEnv
  { _presymtab :: PreSymbolTable n -- for stuff being typechecked
  , _scopes    :: [Scope n]
  , _symtab    :: SymbolTable₃     -- for stuff already typechecked
  }

instance Default (TyEnv n) where
  def = TyEnv HM.empty [HM.empty] HM.empty

makeLenses ''TyEnv

moduleQualifier :: Module σ c → Qualifier
moduleQualifier mod = mod ^. (definitions . to (fmap _qname))

importQualifier :: [Ident] → (Ident → Qualifier) → Qualifier
importQualifier mods modQs = HM.unions $ fmap modQs mods
