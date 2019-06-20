module Statix.Repl.Types where

import System.Console.Haskeline

import Data.HashMap.Strict as HM

import Control.Lens
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Unique as Unique

import Statix.Syntax

-- | The REPL Monad.
type REPL =
  ( StateT REPLState
  ( InputT IO ))

data REPLState = REPLState
  { _globals   :: SymbolTable₃
  , _freshId   :: Integer
  , _imports   :: [Ident]
  , _roots     :: [String]
  , _gen       :: Integer
  }

makeLenses ''REPLState

instance MonadUnique Integer REPL where
  fresh = do
    i ← use freshId
    freshId %= (+1)
    return i

  updateSeed i = modify (set freshId i)

importMod :: Module₃ → REPL ()
importMod mod = do
  let name = mod^.moduleName
  modify (over imports (name:))
  modify (over globals (HM.insert name mod))
