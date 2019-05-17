module Statix.Analysis.Types where

import Data.Default
import Data.HashMap.Strict as HM hiding (map)
import Control.Lens

import Statix.Syntax

import Unification
import Unification.ST

data TCError
  =
  ModuleLocal String TCError
  | WithPosition Pos TCError
  
  -- namer errors
  | DuplicatePredicate Ident
  | UnboundPredicate Ident
  | UnboundVariable Ident
  | MatchCaptures Ident

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

type PreSignature n    = [ (Ident, n) ]
type PrePredicate n    = Predicate (Ident, n) Constraint₁
type PreModule n       = Module Ident Constraint₁
type PreSymbolTable n  = SymbolTable (Ident, n) Constraint₁

type TyRef s           = Class s (Const Type) ()

data TyEnv n = TyEnv
  { _symtab :: PreSymbolTable n
  , _scopes :: [Scope n]
  }

instance Default (TyEnv n) where
  def = TyEnv HM.empty [HM.empty]

makeLenses ''TyEnv

moduleQualifier :: Ident → SymbolTable σ c → Qualifier
moduleQualifier mod syms = (syms HM.! mod) ^. (definitions . to (fmap _qname))

importQualifier :: [Ident] → SymbolTable σ c → Qualifier
importQualifier mods syms = HM.unions $ fmap (flip moduleQualifier syms) (mods)
