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
import Data.Functor.Fixedpoint

import Control.Monad.Except

import Statix.Syntax.Lexer as StxLex
import Statix.Syntax.Parser as StxParser
import Statix.Syntax.Constraint
import Statix.Analysis

import Statix.Repl (REPL, runREPL, printSolution)
import Statix.Repl.Errors
import Statix.Solver

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
  let modname = pack spec

  -- parse the module
  rawmod ← handleErrors $ StxParser.parseModule modname content

  -- Typecheck the module
  mod ← withErrors $ analyze modname HM.empty rawmod

  -- Parse the aterm file
  doc   ← liftIO $ readFile (here </> file)
  aterm ← handleErrors $ AParser.parse doc

  -- solve the main - if it is defined
  let main   = (modname, pack "main")
  let symtab = HM.singleton modname mod
  let wrapper = CApply main [fromATerm aterm]

  solution@(result, sg) ← case HM.lookup (snd main) mod of
    Nothing → handleErrors $ Left $ "Missing main in module " ++ spec
    Just p  → return $ solve symtab wrapper

  case result of
    Left error → liftIO $ do
      putStrLn "Unsatisfiable"
      report error
      putStrLn "Graph: "
      print sg

    Right sol → liftIO $ do
      liftIO $ putStrLn "Satisfied"
      liftIO $ printSolution solution
