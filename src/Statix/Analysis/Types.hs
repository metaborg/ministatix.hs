{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Statix.Analysis.Types where

import Data.Default
import Data.Text hiding (length, head, tail, find)
import Data.HashMap.Strict as HM
import Data.Coerce
import Data.Functor.Identity
import Data.Maybe
import Data.List

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical

data TCError
  = DuplicatePredicate Ident
  | UnboundPredicate Ident
  | UnboundVariable Ident
  | ArityMismatch QName Int Int -- pred, expected, got
  deriving (Show)

-- | Name checking monad
type NCM = ReaderT NameContext (Except TCError)

-- | Type checking monad
type TCM = ExceptT TCError (State SymTab)

data NameContext = NC
  { qualifier :: HashMap Ident QName   -- predicate names → qualified
  , locals    :: [[Ident]]             -- local environment
  }

instance Default NameContext where
  -- Any namecontext should have at least one scope,
  -- the LexicalM interface ensures that the list of active scopes is never empty
  def = NC HM.empty [[]]

qualify :: Ident → NCM QName
qualify n = do
  mq ← asks (HM.lookup n . qualifier)
  case mq of
    Nothing → throwError (UnboundPredicate n)
    Just q  → return q

getPred :: QName → TCM Predicate₁
getPred q = gets (\sym → sym HM.! q)

unfold :: QName → TCM Constraint₁
unfold q = body <$> getPred q

getSig :: QName → TCM Signature
getSig q = sig <$> getPred q

getArity :: QName → TCM Int
getArity q = length <$> params <$> sig <$> getPred q

runTC :: SymTab → TCM a → (Either TCError a, SymTab)
runTC sym c = runIdentity $ runStateT (runExceptT c) sym

runNC :: NameContext → NCM a → Either TCError a
runNC ctx c = runExcept $ runReaderT c ctx

liftNC :: NameContext → NCM a → TCM a
liftNC ctx c = do
  case runNC ctx c of
    Left e  → throwError e
    Right v → return v

instance ScopedM NCM where
  type Binder NCM = Ident
  type Ref    NCM = Ident
  type Datum  NCM = IPath

  enter c     = local (\ctx → ctx { locals = [] : locals ctx }) c

  intros xs c = local (\ctx →
                       let lex = locals ctx
                       in ctx { locals = (xs ++ head lex) : tail lex }) c

  resolve x   = do
    lex ← asks locals
    search x lex

    where
      search :: Text → [[Ident]] → NCM IPath
      search x [] = throwError (UnboundVariable x)
      search x (xs : xss) =
        if elem x xs
          then return (End x)
          else do
            p ← search x xss
            return (Skip p)
