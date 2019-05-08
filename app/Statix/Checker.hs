module Statix.Checker where

import System.Directory
import System.FilePath
import System.Exit

import Data.HashMap.Strict as HM

import Control.Monad.Except
import Control.Monad.ST.Unsafe

import Statix.Syntax

import Statix.Repl (runREPL, printResult)
import Statix.Repl.Types (REPL)
import Statix.Repl.Errors
import Statix.Solver
import Statix.IO

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
main specfile file = runREPL HM.empty $ do
  here'  <- liftIO getCurrentDirectory
  let here = addTrailingPathSeparator here'

  -- Parse and typecheck the specification module
  let modname = specfile
  mod   <- withErrors $ loadModuleFromFile [here] modname specfile

  -- Parse the aterm file
  doc   ← liftIO $ readFile (here </> file)
  aterm ← handleErrors $ AParser.parse doc

  -- Solve the main - if it is defined
  let main   = (modname, "main")
  let symtab = HM.singleton modname mod
  let wrapper = CApply main [fromATerm aterm]

  case HM.lookup (snd main) mod of
    Nothing → handleErrors $ Left $ "Missing main in module " ++ modname
    Just p  → do
      result ← liftIO $ unsafeSTToIO $ solve symtab wrapper
      liftIO $ printResult result

      liftIO $ case result of
        IsUnsatisfiable _ _ → exitFailure
        IsStuck _ → exitFailure
        _ → exitSuccess
