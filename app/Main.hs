module Main where

import System.Directory
import System.FilePath
import System.Exit

import Data.HashMap.Strict as HM

import Control.Lens hiding (argument)
import Control.Monad.Except
import Control.Monad.ST.Unsafe

import Statix.Syntax

import Statix.Repl (runREPL, printResult)
import Statix.Repl.Types
import Statix.Repl.Errors
import Statix.Solver
import Statix.Importer

import ATerms.Syntax.Parser as AParser

import Options.Applicative
import Data.Semigroup ((<>))

data Params = Params
  { includes :: [String]
  , spec     :: String
  , files    :: [String]
  }

params :: Parser Params
params = Params
      <$> many (option str (long "include" <> short 'I' <> help "extend include path"))
      <*> argument str (metavar "SPEC" <> help "the statix specification")
      <*> some (argument str (metavar "FILES..."))

opts = info (params <**> helper)
  ( fullDesc
  <> progDesc "Check FILES against SPEC"
  <> header "ministatix" )

handleErrors :: (ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a) = return a
handleErrors (Left e)  = liftIO $ do
    report e
    exitFailure

withErrors :: (ReplError e) ⇒ ExceptT e REPL a → REPL a
withErrors c = do
  err ← runExceptT c
  handleErrors err

statix :: Params → IO ()
statix params = void $ runREPL HM.empty $ do
  here ← addTrailingPathSeparator <$> liftIO getCurrentDirectory
  let path = here : includes params

  liftIO $ putStrLn "Loading specification..."
  importModule path (spec params)

  -- Parse and typecheck the specification module
  forM (files params) $ \file → do
    liftIO $ putStrLn $ "Checking " ++ file ++ "..."

    -- Parse the aterm file
    doc   ← liftIO $ readFile (here </> file)
    aterm ← handleErrors $ AParser.parse doc

    -- Solve the main - if it is defined
    symtab ← use globals
    let mod = symtab HM.! (spec params)
    let main   = (spec params, "main")
    let wrapper = CApply main [fromATerm aterm]

    case HM.lookup (snd main) mod of
      Nothing → handleErrors $ Left $ "Missing main in module " ++ (spec params)
      Just p  → do
        result ← liftIO $ unsafeSTToIO $ solve symtab wrapper
        liftIO $ printResult result

        liftIO $ case result of
          IsUnsatisfiable _ _ → exitFailure
          IsStuck _ → exitFailure
          _ → exitSuccess

main :: IO ()
main = do
  params ← execParser opts
  statix params
