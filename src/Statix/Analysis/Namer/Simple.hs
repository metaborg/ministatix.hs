module Statix.Analysis.Namer.Simple where

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

-- | Name checking monad
type NCM = ReaderT NameContext (Except TCError)

runNC :: NameContext → NCM a → Either TCError a
runNC ctx c = runExcept $ runReaderT c ctx

instance MonadLex Ident Ident IPath NCM where
  enter     = local (over locals ([]:))

  intros xs = local (over locals (\lex → (xs ++ head lex) : tail lex))

  resolve x = do
    lex ← view locals
    search x lex
    where
      search :: Text.Text → [[Ident]] → NCM IPath
      search x [] = throwError (UnboundVariable x)
      search x (xs : xss) =
        if elem x xs
          then return (End x)
          else do
            p ← search x xss
            return (Skip p)

instance MonadNamer NCM
