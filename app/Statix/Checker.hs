module Statix.Checker where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Console.Haskeline.History
import System.Exit

import Data.Text (Text, pack)
import Data.HashMap.Strict as HM

import Control.Monad.Except

import Statix.Syntax.Lexer as StxLex
import Statix.Syntax.Parser as StxParser
import Statix.Analysis

import Statix.Repl (REPL, runREPL)
import Statix.Repl.Errors

import ATerms.Syntax.Lexer as ALex
import ATerms.Syntax.Parser as AParser

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
  let modname = pack spec

  -- parse the module
  toks   ← handleErrors $ StxLex.lexer content
  rawmod ← handleErrors $ StxParser.runParser modname $ StxParser.parseModule $ toks

  -- Typecheck the module
  mod ← withErrors $ analyze modname HM.empty rawmod

  -- Parse the aterm file
  doc   ← liftIO $ readFile (here </> file)
  aterm ← handleErrors $ AParser.parse doc

  liftIO $ putStrLn "All good!"
  liftIO $ exitSuccess
