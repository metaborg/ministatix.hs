module Statix.Checker where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Console.Haskeline.History
import System.Exit

import Data.HashMap.Strict as HM
import Data.Functor.Fixedpoint

import Control.Monad.Except
import Control.Monad.ST.Unsafe

import Statix.Syntax
import Statix.Syntax.Surface
import Statix.Syntax.Parser as StxParser
import Statix.Analysis

import Statix.Repl (REPL, runREPL, printResult)
import Statix.Repl.Errors
import Statix.Solver
import Statix.Graph
import Statix.Solver.Monad
import Statix.Solver.Types

import ATerms.Syntax.Lexer as ALex
import ATerms.Syntax.Parser as AParser

import Debug.Trace

handleErrors :: (ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a) = return a
handleErrors (Left e)  = liftIO $ do
    report e
    exitFailure

withErrors :: (ReplError e) ⇒ ExceptT e REPL a → REPL a
withErrors c = do
  err ← runExceptT c
  handleErrors err

main :: String → String → IO ()
main spec file = runREPL HM.empty $ do
  here     ← liftIO getCurrentDirectory
  let path = here </> spec
  content  ←  liftIO $ readFile path
  let modname = spec

  -- parse the module
  rawmod ← handleErrors $ StxParser.parseModule modname content
  let rawmod' = desugarMod rawmod

  -- Typecheck the module
  mod ← withErrors $ analyze modname HM.empty rawmod'

  -- Parse the aterm file
  doc   ← liftIO $ readFile (here </> file)
  aterm ← handleErrors $ AParser.parse doc

  -- solve the main - if it is defined
  let main   = (modname, "main")
  let symtab = HM.singleton modname mod
  let wrapper = CApply main [fromATerm aterm]

  case HM.lookup (snd main) mod of
    Nothing → handleErrors $ Left $ "Missing main in module " ++ spec
    Just p  → do
      result ← liftIO $ unsafeSTToIO $ solve symtab wrapper
      liftIO $ printResult result

      liftIO $ case result of
        IsUnsatisfiable _ _ → exitFailure
        IsStuck _ → exitFailure
        _ → exitSuccess
