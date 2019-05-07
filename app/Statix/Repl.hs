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
self :: Getting String REPLState String
self = gen . (to $ \g → "repl-" ++ show g)

main :: Getting String REPLState String
main = gen . (to $ \g → "main" ++ show g)

runREPL :: SymbolTable → REPL a → IO a
runREPL sym c = runInputT (defaultSettings { historyFile = Just ".statix" }) $ evalStateT c (REPLState sym 0 [] 0)

instance MonadUnique Integer REPL where
  fresh = do
    i ← use freshId
    freshId %= (+1)
    return i

  updateSeed i = modify (set freshId i)

prompt :: REPL Cmd
prompt = do
  cmd ← lift $ getInputLine "► "
  case cmd of
    Nothing  → prompt
    Just cmd → handleErrors (readEither cmd)

printGraph :: IntGraph Label String → IO ()
printGraph (IntGraph sg) =
  forM_ (IM.elems sg) $ \(IntNode id es d) → do
    putStr "∇ "
      >> putStr (show id)
      >> putStr " ─◾ " >> putStr d
      >> putStr "\n"

    forM_ es $ \(IntEdge l d n) → do
      putStr "\t-[ "
        >> putStr (show l)
        >> printDatum d
        >> putStr " ]-> " >> print n
  where
    printDatum = maybe (return ()) (\t → putStr $ "(" ++ t ++ ")")


printResult :: Result s → IO ()
printResult (IsSatisfied φ sg) = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn "⟨✓⟩ Satisfiable"
  setSGR [Reset]
  putStrLn "⟪ Unifier ⟫"
  -- TODO putStrLn (formatUnifier φ)
  putStrLn ""
  putStrLn "⟪ Graph ⟫"
  printGraph sg
  putStrLn ""
printResult (IsUnsatisfiable e gr) = do
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "⟨×⟩ Unsatisfiable"
  setSGR [Reset]
  putStrLn "⟪ Trace ⟫"
  report e
  putStrLn ""
  putStrLn "⟪ Graph ⟫"
  printGraph gr
  putStrLn ""
printResult (IsStuck q) = do
  setSGR [SetColor Foreground Vivid Yellow]
  putStrLn "⟨×⟩ Stuck, with queue:"
  setSGR [Reset]
  mapM_ putStrLn q
  putStrLn ""

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
  putStrLn $ "⟨✓⟩ Imported module "
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
  c        ← handleErrors $ parseConstraint this rawc
  let c'   = desugar c
  mod      ← withErrors $ analyze this symtab (Mod imps [Pred (this, main) [] c'])

  -- import the module
  importMod this mod
  modify (over gen (+1))

  liftIO $ runST $ fmap printResult (solve symtab (body $ mod HM.! main))

  -- rinse and repeat
  κ

handler κ (Define p) = do
  this   ← use self
  imps   ← use imports
  symtab ← use globals

  pr    ← handleErrors $ parsePredicate this p
  let pr' = desugarPred pr
  mod   ← withErrors $ analyze this symtab (Mod imps [pr'])

  -- import the predicate into the symboltable
  importMod this mod
  modify (over gen (+1))

  -- rinse and repeat
  κ

handler κ (Import file) = do
  here     ← liftIO getCurrentDirectory
  let path = here </> file
  content  ← liftIO $ readFile path
  let modname = file

  symtab ← use globals

  -- parse the module
  rawmod ← handleErrors $ parseModule modname content
  let rawmod' = desugarMod rawmod

  -- Typecheck the module
  mod ← withErrors $ analyze modname symtab rawmod'

  -- Import the typechecked module into the symboltable
  importMod modname mod

  -- rinse and repeat
  κ

handler κ (Type pred) = do
  imps   ← use imports
  symtab ← use globals
  let q = importsQualifier imps symtab

  case (symtab !!!) <$> HM.lookup pred q of
    Just p  → liftIO $ putStrLn $
      pred
        ++ " :: "
        ++ (intercalate " → "
            (fmap (\(n,t) → "(" ++ n ++ " : " ++ show t ++ ")") $ reverse $ sig p))
        ++ " → Constraint"
    Nothing → liftIO $ putStrLn $ "No predicate named: " ++ pred

  κ

handler κ Help = do
  liftIO $ putStrLn $ helpText
  κ

handler κ Quit = do
  liftIO exitSuccess
 
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
