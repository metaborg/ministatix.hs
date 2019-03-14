module Repl where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath

import Data.HashMap.Strict as HM
import Data.Char
import Text.Read hiding (lift, get)
import qualified Data.Text as Text

import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Reader hiding (liftIO)

import Statix.Syntax.Constraint
import Statix.Solver
import Statix.Solver.Types
import Statix.Syntax.Parser
import Statix.Analysis.Types hiding (liftNC)
import Statix.Analysis.Checker

{- A means to handling various errors in the REPL -}
class ReplError e where
  report :: e → IO ()

instance ReplError TCError where
  report e = putStrLn $ show e

instance ReplError String where
  report e = putStrLn e

handleErrors :: (Show e, ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a)  = return a
handleErrors (Left err) = do
  liftIO $ putStrLn $ show err
  loop

{- The REPL Monad -}
type REPL a  = ReaderT Context (StateT SymbolTable IO) a

runRepl :: Context → SymbolTable → REPL a → IO a
runRepl ctx sym c = evalStateT (runReaderT c ctx) sym

liftIO :: IO a → REPL a
liftIO c = lift $ lift c

liftNC :: NCM a → REPL a
liftNC c = do
  ctx ← ask
  handleErrors $ runNC ctx c
  
liftTC :: TCM a → REPL a
liftTC c = do
  sym ← get
  handleErrors $ runTC sym c

liftParser :: String → ParserM a → REPL a
liftParser mod c = handleErrors $ runParser mod c

-- | Repl Commands
-- :def <pred>    - define a new predicate <pred>
-- :import <path> - load a statix module <path>
-- <constraint>   - try to solve <constraint>
data Cmd
  = Define String
  | Main String
  | Import String

-- | Cmd parser
instance Read Cmd where

  readsPrec _ s

    -- if starts with a colon, then we parse a command
    | (':':xs) ← s =
        case (span isAlpha xs) of
          ("def", ys) →
            [(Define ys, [])]
          ("import", ys) →
            let path = Text.unpack $ Text.strip $ Text.pack ys in
            [(Import path, [])]
          otherwise → []

    -- otherwise it is just a constraint
    | otherwise   = [(Main s, [])]

prompt :: IO ()
prompt = do
  putStr "► "
  hFlush stdout

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

reportImports :: Module → IO ()
reportImports mod = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn ""
  putStrLn $ "  ⟨✓⟩ Imported module " ++ modname mod
  setSGR [Reset]
  putStrLn $ showModuleContent mod
  putStrLn ""

-- | We trick the type checker by typing loop as `REPL a`.
-- This allows us to handle errors by outputting some string and resuming the loop.
loop :: REPL a
loop = do
  liftIO prompt

  -- read a command
  cmd ← (liftIO $ readEither <$> getLine) >>= handleErrors

  -- dispatch between different REPL operations
  case cmd of

    (Main rawc)   → do
      c   ← liftParser "repl" $ (parseConstraint (lexer rawc))
      cok ← liftNC $ checkConstraint c
      solution ← gets (\sym → solve sym cok)
      liftIO $ putStrLn ""
      liftIO $ printSolution solution
      loop

    (Define p) → do
      pr   ← liftParser "repl" (parsePredicate (lexer p))
      prty ← liftNC $ checkPredicate pr
      let σ = sig prty
      lift $ modify (HM.insert (qname σ) prty)
      local (HM.insert (predname σ) (qname σ)) loop

    (Import file) → do
      here     ← liftIO getCurrentDirectory
      let path = here </> file
      content  ← liftIO $ readFile path
      let modname = takeBaseName file
      rawmod   ← liftParser modname $ parseModule $ lexer content
      mod      ← liftTC $ checkMod modname rawmod

      -- insert into the symboltable
      modify (importMod mod)
      liftIO $ reportImports mod

      -- update the context
      local (\ctx → HM.union (fmap (qname . sig) (defs mod)) ctx) loop

-- | Run the repl in IO
repl :: IO ()
repl = runRepl HM.empty HM.empty loop
