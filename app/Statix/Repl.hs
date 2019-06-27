module Statix.Repl where

import System.Console.ANSI
import System.Directory
import System.Console.Haskeline
import System.Exit

import Data.List
import Data.Default
import Data.HashMap.Strict as HM
import Data.IntMap.Strict as IM
import Text.Read hiding (lift, get, lex)

import Control.Lens
import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.IO.Class
import Control.Monad.ST
import Control.Monad.Unique()

import Statix.Graph

import Statix.Syntax
import Statix.Syntax.Surface
import Statix.Syntax.Parser

import Statix.Solver
import Statix.Solver.Debug

import Statix.Analysis.Types hiding (self)
import Statix.Analysis

import Statix.Repl.Command
import Statix.Repl.Errors

import Statix.Repl.Types
import Statix.Importer

-- | The module name for the current generation of the REPL
self :: Getting String REPLState String
self = gen . (to $ \g → "repl-" ++ show g)

main :: Getting String REPLState String
main = gen . (to $ \g → "main" ++ show g)

runREPL :: SymbolTable₃ → REPL a → IO a
runREPL sym c =
  runInputT
    (defaultSettings { historyFile = Just ".statix" }) $
    evalStateT c (REPLState sym 0 [] [] 0)

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
  putStrLn (showUnifier φ)
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
printResult (IsStuck q gr) = do
  setSGR [SetColor Foreground Vivid Yellow]
  putStrLn "⟨×⟩ Stuck, with queue:"
  setSGR [Reset]
  mapM_ putStrLn q
  putStrLn ""
  putStrLn "⟪ Partial graph ⟫"
  printGraph gr
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

reportImports :: Module₂ → IO ()
reportImports mod = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn ""
  putStrLn $ "⟨✓⟩ Imported module "
  setSGR [Reset]

handler :: REPL a → Cmd → REPL a
handler κ (Main rawc) = do
  main   ← use main
  this   ← use self
  imps   ← use imports
  symtab ← use globals

  -- parse and analyze the constraint as a singleton module
  c        ← handleErrors $ parseConstraint this rawc
  let c'   = desugar c
  mods     ← withErrors $ analyze [RawMod this imps [Pred def (this, main) [] c']] symtab


  -- import the module
  forM_ mods importMod
  modify (over gen (+1))

  -- run the defined main
  symtab ← use globals
  liftIO $ runST $ fmap printResult
    (solve symtab (mods^.to (HM.! this).definitions.to (HM.! main).body))

  -- rinse and repeat
  κ

handler κ (Define p) = do
  this    ← use self
  imps    ← use imports
  symtab  ← use globals

  pr      ← handleErrors $ parsePredicate this p
  let pr' = desugarPred pr
  mods    ← withErrors $ analyze [RawMod this imps [pr']] symtab

  -- import the predicate into the symboltable
  forM_ mods importMod 
  modify (over gen (+1))

  -- rinse and repeat
  κ

handler κ (Import name) = do
  -- load the imported module
  here ← liftIO getCurrentDirectory
  rts  ← use roots
  withErrors $ importModule rts name

  -- rinse and repeat
  κ

handler κ (Type pred) = do
  imps   ← use imports
  symtab ← use globals
  let q = importQualifier imps (\m → moduleQualifier $ symtab HM.! m)

  case HM.lookup pred q >>= \qn → symtab^.lookupPred qn of
    Just p  → liftIO $ putStrLn $
      pred
        ++ " :: "
        ++ showPredType p
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
repl :: [String] → IO ()
repl rts = do
  putStrLn "Ministatix 0.1 (type :help for help)"
  runREPL HM.empty $ do
    roots %= const rts
    loop
 
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
