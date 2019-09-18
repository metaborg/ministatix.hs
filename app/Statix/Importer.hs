module Statix.Importer where

import Data.List (intercalate)
import qualified Data.HashMap.Strict as HM

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import System.Directory (doesFileExist, makeAbsolute)
import System.FilePath

import Statix.Syntax
import Statix.Repl.Types (REPL, importMod)
import Statix.Repl.Errors
import Statix.Analysis (analyze)
import Statix.Analysis.Types
import Statix.Syntax.Parser (parseModule)
import Statix.Syntax.Surface (desugarMod, SurfaceM(..))

type ImportStack = [Ident]
type RawSymboltable = [SurfaceM Predicate₀]
type Importer = ReaderT ImportStack (StateT RawSymboltable (ExceptT ImportError IO))

runImporter :: Importer a → IO (Either ImportError (a, RawSymboltable))
runImporter ma = runExceptT $ runStateT (runReaderT ma []) []

data ImportError
  = ImportErr ImportStack String
  | ParseErr ImportStack String
  | TypeErr Ident TCError

printStack = mapM (\mod → putStrLn $ "├ " ++ mod) . reverse

instance ReplError ImportError where
  report (ImportErr stack e) = do
    putStrLn $ "Loading " ++ head stack ++ " failed."
    printStack stack
    report e
  report (ParseErr stack e) = do
    putStrLn $ "Loading " ++ head stack ++ " failed."
    printStack stack
    report e
  report (TypeErr mod e) = do
    putStrLn $ "Loading " ++ mod ++ " failed."
    report e

-- | Resolves a module to its absolute path, if any.
resolveModule :: [FilePath] → Ident → Importer FilePath
resolveModule rootpaths name = do
  paths ← liftIO $ mapM (\root → getModulePath root name) rootpaths
  modulePaths ← liftIO $ filterM doesFileExist paths
  case modulePaths of
    [path]    → return path
    []        → importErr name ("Module " ++ name ++ " not found at: " ++ (intercalate ", " paths))
    mpaths    → importErr name ("Ambiguous module " ++ name ++ ": " ++ (intercalate ", " mpaths))
  where
    repl '/'  = '_'
    repl '\\' = '_'
    repl '.'  = '/'
    repl x    = x

    nameToPath p = fmap repl p ++ ".mstx"

    getModulePath root name = do
      root ← makeAbsolute root
      return $ root </> nameToPath name

-- | Recursively load raw modules
loadModule :: [FilePath] → Ident → Importer ()
loadModule rootpaths name = do
  liftIO $ putStrLn $ "Loading module " ++ name ++ "..."
  path   ← resolveModule rootpaths name
  rawmod@(RawMod _ imps orders defs) ← loadModuleFromFile rootpaths name path

  -- push the module name to the stack
  local (name:) $ do
    stack ← ask

    -- iterate recursively over imports that we have not seen yet
    forM_ imps $ \imp → 
      if imp `elem` stack
      then return ()
      else do
        symtab ← get
        if any (\(RawMod name _ _ _) → name == imp) symtab
          then return ()
          else loadModule rootpaths imp

  modify (rawmod:)

typeErr :: Ident → TCError → Importer a
typeErr name msg = do
  stack ← ask
  throwError $ TypeErr name msg

importErr :: Ident → String → Importer a
importErr mod msg = do
  stack ← ask
  throwError $ ImportErr (mod:stack) msg

wontParse :: Ident → String → Importer a
wontParse mod msg = do
  stack ← ask
  throwError $ ParseErr (mod:stack) msg

-- | Load and parse a module from file
loadModuleFromFile :: [FilePath] → Ident → FilePath → Importer (SurfaceM Predicate₀)
loadModuleFromFile rootpaths name path = do
  content ← liftIO $ readFile path
  loadModuleFromString rootpaths name content

loadModuleFromString :: [FilePath] → Ident → String → Importer (SurfaceM Predicate₀)
loadModuleFromString rootpaths name content = do
  rawmod  ← either (wontParse name) return $ parseModule name content
  return $ desugarMod rawmod

-- | Recursively import modules into symboltable
importModule :: [FilePath] → Ident → ExceptT ImportError REPL ()
importModule roots name = do
  -- recursively collect the modules to be analyzed
  rawmods      ← liftIO $ runImporter (loadModule roots name)
  (_, rawmods) ← liftEither rawmods

  -- analyze them
  symtab ← withExceptT (TypeErr name) $ analyze rawmods HM.empty

  -- import them
  lift $ forM_ symtab importMod
