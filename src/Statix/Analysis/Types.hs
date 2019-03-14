module Statix.Analysis.Types where

import Data.HashMap.Strict as HM
import Data.Coerce
import Data.Functor.Identity

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable

data TCError
  = DuplicatePredicate String
  | UnboundPredicate String
  | ArityMismatch QName Int Int -- pred, expected, got
  deriving (Show)

-- | Name checking monad
type NCM = ReaderT Context (Except TCError)

-- | Type checking monad
type TCM = ExceptT TCError (State SymbolTable)

type Context = HashMap String QName

qualify :: RawName → NCM QName
qualify n = do
  mq ← asks (HM.lookup n)
  case mq of
    Nothing → throwError (UnboundPredicate n)
    Just q  → return q

getPred :: QName → TCM (Predicate QName)
getPred q = gets (\sym → sym HM.! q)

unfold :: QName → TCM (Constraint QName RawTerm)
unfold q = body <$> getPred q

getSig :: QName → TCM Signature
getSig q = sig <$> getPred q

getArity :: QName → TCM Int
getArity q = length <$> params <$> sig <$> getPred q

runTC :: SymbolTable → TCM a → (Either TCError a, SymbolTable)
runTC sym c = runIdentity $ runStateT (runExceptT c) sym

runNC :: Context → NCM a → Either TCError a
runNC ctx c = runExcept $ runReaderT c ctx

liftNC :: Context → NCM a → TCM a
liftNC ctx c = do
  case runNC ctx c of
    Left e  → throwError e
    Right v → return v
