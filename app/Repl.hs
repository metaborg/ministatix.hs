{-# LANGUAGE TupleSections #-}
module Repl where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Exit

import Data.Default
import Data.HashMap.Lazy as HM
import Data.Char
import Data.Functor.Identity
import Text.Read hiding (lift, get)
import qualified Data.Text as Text
import Data.Maybe

import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Reader hiding (liftIO)

import Statix.Syntax.Parser
import Statix.Syntax.Constraint

import Statix.Solver
import Statix.Solver.Types

import Statix.Analysis.Types hiding (liftNC)
import Statix.Analysis.Symboltable
import Statix.Analysis

{- A means to handling various errors in the REPL -}
class ReplError e where
  report :: e → IO ()

instance ReplError TCError where
  report = print

instance ReplError String where
  report = putStrLn

handleErrors :: (Show e, ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a)  = return a
handleErrors (Left err) = do
  liftIO $ print err
  liftIO $ putStrLn "(type :help for help)"
  loop

{- The REPL Monad -}
type REPL a  = ReaderT NameContext (StateT SymTab (InputT IO)) a

runRepl :: NameContext → SymTab → REPL a → IO a
runRepl ctx sym c = runInputT defaultSettings $ evalStateT (runReaderT c ctx) sym

liftIO :: IO a → REPL a
liftIO c = lift $ lift $ lift c

liftNC :: NCM a → REPL a
liftNC c = do
  ctx ← ask
  handleErrors $ runNC ctx c
  
liftTC :: (forall s . TCM s a) → REPL a
liftTC c = do
  symtab ← get
  (a, symtab') ← handleErrors (runTC symtab c)
  put symtab'
  return a

liftParser :: Text.Text → ParserM a → REPL a
liftParser mod c = handleErrors $ runParser mod c

-- | Repl Commands
-- :def <pred>    - define a new predicate <pred>
-- :import <path> - load a statix module <path>
-- <constraint>   - try to solve <constraint>
data Cmd
  = Define String
  | Main String
  | Import String
  | Nop
  | Help
  | Quit

-- | Cmd parser
instance Read Cmd where

  readsPrec _ s
    -- if it's empty, just continue
    | all isSpace s = [(Nop, "")]
    -- if starts with a colon, then we parse a command
    | (':':xs) ← s =
        maybeToList $ (,"")
        <$> uncurry
        readCmd (span isAlpha xs)
    -- otherwise it is just a constraint
    | otherwise    = [(Main s, "")]

readCmd :: String -> String -> Maybe Cmd
readCmd "def"    = Just <$> Define
readCmd "d"      = readCmd "def"
readCmd "import" = Just <$> \s -> Import (Text.unpack $ Text.strip $ Text.pack s)
readCmd "i"      = readCmd "import"
readCmd "help"   = Just <$> const Help
readCmd "h"      = readCmd "help"
readCmd "quit"   = Just <$> const Quit
readCmd "q"      = readCmd "quit"
readCmd _        = const Nothing


prompt :: REPL Cmd
prompt = do
  cmd ← lift $ lift $ getInputLine "► "
  case cmd of
    Nothing  → prompt
    Just cmd → handleErrors (readEither cmd)

printSolution :: Solution → IO ()
printSolution solution =
  case solution of
    Left e → do
      setSGR [SetColor Foreground Vivid Red]
      putStrLn $ "  ⟨×⟩ - " ++ show e
      putStrLn ""
      setSGR [Reset]
    Right (φ, g) → do
      setSGR [SetColor Foreground Dull Green]
      putStrLn "  ⟨✓⟩ Satisfiable"
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ♯ Unifier"
      setSGR [Reset]
      putStrLn φ
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ♯ Graph"
      setSGR [Reset]
      print g
      setSGR [Reset]

reportImports :: Module IPath Term₁ → IO ()
reportImports mod = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn ""
  putStrLn $ "  ⟨✓⟩ Imported module " ++ Text.unpack (modname mod)
  setSGR [Reset]
  putStrLn $ showModuleContent mod
  putStrLn ""

-- | We trick the type checker by typing loop as `REPL a`.
-- This allows us to handle errors by outputting some string and resuming the loop.
loop :: REPL a
loop = do
  cmd ← prompt

  -- dispatch between different REPL operations
  case cmd of

    (Main rawc)   → do
      c   ← liftParser (Text.pack "repl") $ (parseConstraint (lexer rawc))
      ctx ← ask
      cok ← liftTC $ analyze ctx c
      solution ← gets (\sym → solve sym cok)
      liftIO $ putStrLn ""
      liftIO $ printSolution solution
      loop

    (Define p) → do
      pr    ← liftParser (Text.pack "repl") (parsePredicate (lexer p))
      ctx   ← ask
      prty  ← liftTC $ analyzeP ctx pr
      let σ = sig prty
      local (\nc →
               nc { qualifier = HM.insert (predname σ) (qname σ) (qualifier nc) }) loop

    (Import file) → do
      here     ← liftIO getCurrentDirectory
      let path = here </> file
      content  ← liftIO $ readFile path
      let modname = Text.pack $ takeBaseName file

      -- parse the module
      rawmod   ← liftParser modname $ parseModule $ lexer content

      -- analyze it
      ctx      ← ask
      mod      ← liftTC $ analyzeM ctx modname rawmod

      -- update the local context
      local
        (\nc → nc { qualifier = HM.union (fmap (qname . sig) (defs mod)) (qualifier nc) })
        loop

    Help -> do
      liftIO $ putStrLn $ unlines [
        "Commands:",
        "  :def p            -- Defines a predicate p",
        "  :import f         -- Imports constraints from a file f",
        "  :help             -- Prints this help",
        "  :quit             -- Quits",
        "Constraint Syntax:",
        "  { x, .. } C       -- Extensionally quantifies variables x, .. in constraint C",
        "  ( C )             -- Group constraints C",
        "  C₁, C₂            -- Asserts constraints C₁ and C₂",
        "  t₁ = t₂           -- Asserts equality of terms t₁ and t₂",
        "  true              -- Asserts nothing",
        "  false             -- Asserts false",
        "  new x             -- Asserts that you own a node x in the graph",
        "  s₁ -[ℓ]-> s₂      -- Asserts that you own an edge from node s₁ to node s₂ with label ℓ in the graph",
        "  query s r as z    -- Query the graph from s with regex r as z",
        "  one(t, t')        -- Asserts that term t' is a set with a single element t",
        "  every x ζ C       -- Asserts constraint C for every x in set ζ"
        ]
      loop

    Quit -> do
      liftIO $ exitSuccess
      loop
    
    Nop -> loop

-- | Run the repl in IO
repl :: IO ()
repl = runRepl def HM.empty loop_entry

-- | Loop entry point
loop_entry :: REPL a
loop_entry = do
  liftIO $ putStrLn "Ministatix REPL"
  loop
