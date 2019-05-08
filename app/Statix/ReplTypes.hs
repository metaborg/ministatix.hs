module Statix.ReplTypes where

import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Console.Haskeline.History
import System.Exit

import Data.Default
import Data.List
import Data.HashMap.Strict as HM
import Data.IntMap.Strict as IM
import Data.Functor.Identity
import qualified Data.Text.IO as TIO
import Text.Read hiding (lift, get, lex)

import Control.Lens
import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.IO.Class
import Control.Monad.ST
import Control.Monad.Unique as Unique

import Debug.Trace

import Statix.Graph

import Statix.Syntax
import Statix.Syntax.Surface
import Statix.Syntax.Parser

import Statix.Solver
import Statix.Solver.Types

import Statix.Analysis.Types hiding (self)
import Statix.Analysis.Symboltable
import Statix.Analysis

import Statix.Repl.Command
import Statix.Repl.Errors

import Statix.Imports

-- | The REPL Monad.
type REPL =
  ( StateT REPLState
  ( InputT IO ))

data REPLState = REPLState
  { _globals   :: SymbolTable
  , _freshId   :: Integer
  , _imports   :: [Ident]
  , _gen       :: Integer
  }

makeLenses ''REPLState

instance MonadUnique Integer REPL where
  fresh = do
    i ← use freshId
    freshId %= (+1)
    return i

  updateSeed i = modify (set freshId i)

importMod :: Ident → Module → REPL ()
importMod i mod = do
  modify (over imports (i:))
  modify (over globals (HM.insert i mod))
