module Statix.Repl where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Console.Haskeline.History
import System.Exit

import Data.Default
import Data.List
import Data.HashMap.Strict as HM
import Data.Functor.Identity
import qualified Data.Text as Text
import Text.Read hiding (lift, get, lex)

import Control.Lens
import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.IO.Class
import Control.Monad.ST
import Control.Monad.Unique as Unique

import Debug.Trace

import Statix.Syntax.Parser
import Statix.Syntax.Lexer
import Statix.Syntax.Constraint

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
  { _globals :: SymbolTable
  , _freshId :: Integer
  , _imports :: [Ident]
  , _gen     :: Integer
  }

makeLenses ''REPLState

-- | The module name for the current generation of the REPL
self :: Getting Text.Text REPLState Text.Text
self = gen . (to $ \g → "repl-" ++ show g) . to Text.pack

main :: Getting Text.Text REPLState Text.Text
main = gen . (to $ \g → "main" ++ show g) . to Text.pack

runREPL :: SymbolTable → REPL a → IO a
runREPL sym c = runInputT (defaultSettings { historyFile = Just ".statix" }) $ evalStateT c (REPLState sym 0 [] 0)

instance MonadUnique Integer REPL where
  fresh = do
    i ← use freshId
    freshId %= (+1)
    return i

  updateSeed i = modify (set freshId i)

liftParser :: Ident → ParserM a → REPL a
liftParser modName c = handleErrors $ runParser modName c

prompt :: REPL Cmd
prompt = do
  cmd ← lift $ getInputLine "► "
  case cmd of
    Nothing  → prompt
    Just cmd → handleErrors (readEither cmd)

printSolution :: Solution → IO ()
printSolution solution =
  case solution of
    Left e → do
      setSGR [SetColor Foreground Vivid Red]
      putStrLn $ "  ⟨✗⟩ - " ++ show e
      putStrLn ""
      setSGR [Reset]
    Right (φ, g) → do
      setSGR [SetColor Foreground Dull Green]
      putStrLn "  ⟨✓⟩ Satisfiable"
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ⟪ Unifier ⟫"
      setSGR [Reset]
      putStrLn φ
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ⟪ Graph ⟫"
      setSGR [Reset]
      print g
      setSGR [Reset]

withErrors :: (ReplError e) ⇒ ExceptT e REPL a → REPL a
withErrors c = do
  err ← runExceptT c
  handleErrors err

handleErrors :: (ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a)  = return a
handleErrors (Left err) = do
  liftIO $ report err
  loop

reportImports :: Module → IO ()
reportImports mod = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn ""
  putStrLn $ "  ⟨✓⟩ Imported module "
  setSGR [Reset]
  -- putStrLn $ showModuleContent mod
  -- putStrLn ""

importMod :: Ident → Module → REPL ()
importMod i mod = do
  modify (over imports (i:))
  modify (over globals (HM.insert i mod))

handler :: REPL a → Cmd → REPL a
handler κ (Main rawc) = do
  main   ← use main
  this   ← use self
  imps   ← use imports
  symtab ← use globals

  -- parse and analyze the constraint as a singleton module
  toks     ← handleErrors $ lexer rawc
  c        ← liftParser this $ (parseConstraint toks) 
  mod      ← withErrors $ analyze symtab (Mod this imps [Pred (this, main) [] c])

  -- import the module
  importMod this mod
  modify (over gen (+1))

  let solution = solve symtab (body $ mod HM.! main)

  -- output solution
  liftIO $ putStrLn ""
  liftIO $ printSolution solution

  -- rinse and repeat
  κ

handler κ (Define p) = do
  this   ← use self
  imps   ← use imports
  symtab ← use globals

  toks  ← handleErrors $ lexer p
  pr    ← liftParser this (parsePredicate toks)
  mod   ← withErrors $ analyze symtab (Mod this imps [pr])

  -- import the predicate into the symboltable
  importMod this mod
  modify (over gen (+1))

  -- rinse and repeat
  κ

handler κ (Import path) = do
  symtab ← use globals

  -- parse the module
  here     ← liftIO getCurrentDirectory
  let modName = Text.pack path
  let modPath = resolveModule here modName
  r <- liftIO $ readModuleIO modName modPath
  rawmod <- handleErrors $ r
  -- toks   ← handleErrors $ lexer content
  -- rawmod ← liftParser modName $ parseModule $ toks

  -- Typecheck the module
  mod ← withErrors $ analyze symtab rawmod

  -- Import the typechecked module into the symboltable
  importMod modName mod

  -- rinse and repeat
  κ

handler κ (Type pred) = do
  imps   ← use imports
  symtab ← use globals
  let q = importsQualifier imps symtab

  case (symtab !!!) <$> HM.lookup pred q of
    Just p  → liftIO $ putStrLn $
      Text.unpack pred
        ++ " :: "
        ++ (intercalate " → "
            (fmap (\(n,t) → "(" ++ Text.unpack n ++ " : " ++ show t ++ ")") $ reverse $ sig p))
        ++ " → Constraint"
    Nothing → liftIO $ putStrLn $ "No predicate named: " ++ Text.unpack pred

  κ

handler κ Help = do
  liftIO $ putStrLn $ helpText
  κ

handler κ Quit = do
  liftIO $ exitSuccess
  κ
 
handler κ Nop = κ

-- | We trick the type checker by typing loop as `REPL a`.
-- This allows us to handle errors by outputting some string and resuming the loop.
loop :: REPL a
loop = do
  cmd  ← prompt
  handler loop cmd

-- | Run the repl in IO
repl :: IO ()
repl = do
  liftIO $ putStrLn "Ministatix 0.1 (type :help for help)"
  runREPL HM.empty loop
 
helpText :: String
helpText = unlines [
  "Commands:",
  "  :def p                     -- Defines a predicate p",
  "  :import f                  -- Imports constraints from a file f",
  "  :type p                    -- Print the type of p",
  "  :help                      -- Prints this help",
  "  :quit                      -- Quits",
  "Constraint Syntax:",
  "  { x, .. } C                -- Extensionally quantifies variables x, .. in constraint C",
  "  C₁, C₂                     -- Asserts constraints C₁ and C₂",
  "  t₁ = t₂                    -- Asserts equality of terms t₁ and t₂",
  "  true                       -- Asserts true",
  "  false                      -- Asserts false",
  "  new x                      -- Asserts that you own a node x in the graph",
  "  x -> t                     -- Assert node x carries datum t",
  "  s₁ -[l]-> s₂               -- Asserts that you own an edge from node s₁ to node s₂ with label l in the graph",
  "  query s r as z             -- Query the graph from s with regex r as z",
  "  only(ζ, t')                -- Asserts that ζ is a singleton set containing t",
  "  every x ζ C                -- Asserts constraint C for every x in set ζ",
  "  min   ζ e ζ'               -- Asserts that ζ' is the minimum of ζ using path order expression e",
  "  match t₁ { t₂ -> C | ... } -- Assert C if t₁ and t₂ are equal"
  ]
