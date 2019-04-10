{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
module Repl where

import System.IO hiding (liftIO)
import System.Console.ANSI
import System.Directory
import System.FilePath
import System.Console.Haskeline
import System.Exit

import Data.Default
import Data.HashMap.Strict as HM
import Data.Char
import Data.Functor.Identity
import Text.Read hiding (lift, get, lex)
import qualified Data.Text as Text
import Data.Maybe

import Control.Lens
import Control.Monad.Except hiding (liftIO)
import Control.Monad.State  hiding (liftIO)
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.IO.Class
import Control.Monad.ST
import Control.Monad.Unique as Unique
import Control.Monad.Equiv as Equiv

import Unification
import Unification.ST

import Statix.Syntax.Parser
import Statix.Syntax.Constraint

import Statix.Solver
import Statix.Solver.Types

import Statix.Analysis.Types hiding (self)
import Statix.Analysis.Symboltable
import Statix.Analysis

{- A means to handling various errors in the REPL -}
class ReplError e where
  report :: e → IO ()

instance ReplError TCError where
  report = print

instance ReplError String where
  report = putStrLn

-- | The REPL Monad.
type REPL =
  ( ReaderT REPLEnv
  ( StateT REPLState
  ( InputT IO )))

data REPLState = REPLState
  { _globals :: SymbolTable
  , _freshId :: Int
  }

data REPLEnv = REPLEnv
  { _lexical :: NameContext
  , _typing  :: PreModuleTyping RealWorld
  , _self    :: Ident
  }

makeLenses ''REPLEnv
makeLenses ''REPLState

runREPL :: NameContext → SymbolTable → REPL a → IO a
runREPL ctx sym c =
  let replmod = (Text.pack "repl") in
    runInputT defaultSettings $
    evalStateT (runReaderT c (REPLEnv ctx HM.empty replmod)) (REPLState sym 0)

instance MonadUnique Int REPL where
  fresh = do
    i ← use freshId
    freshId %= (+1)
    return i

instance (Unifiable f) ⇒ MonadEquiv (Class RealWorld f v) REPL (Rep (Class RealWorld f v) f v) where

  newClass         = liftIO . stToIO . newClass
  repr             = liftIO . stToIO . repr
  description      = liftIO . stToIO . description
  modifyDesc c     = liftIO . stToIO . modifyDesc c
  unionWith n n' f = liftIO $ stToIO $ Equiv.unionWith n n' f

instance MonadAnalysis REPL where
  type Typer REPL = TCM RealWorld
  type Namer REPL = NCM

  imports p = do
    modify (over globals (HM.insert (qname p) p))
    
  namer c = do
    ctx ← view lexical
    let a = runNC ctx c
    handleErrors a

  typer c = do
    (REPLEnv _ pt self)  ← ask
    (REPLState symtab i) ← get

    let st = runTC (def { _self = self, _modtable = pt, _symty = symtab}) c i
    (a, i') ← (liftIO $ stToIO st) >>= handleErrors

    -- ensure that the fresh names remain fresh
    modify (set freshId i')

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

handleErrors :: (Show e, ReplError e) ⇒ Either e a → REPL a
handleErrors (Right a)  = return a
handleErrors (Left err) = do
  liftIO $ putStrLn $ show err
  loop

reportImports :: Module → IO ()
reportImports mod = do
  setSGR [SetColor Foreground Dull Green]
  putStrLn ""
  putStrLn $ "  ⟨✓⟩ Imported module "
  setSGR [Reset]
  -- putStrLn $ showModuleContent mod
  -- putStrLn ""

handler :: REPL a → Cmd → REPL a
handler κ (Main rawc) = do
  this ← view self

  -- interpreter pipeline for a single constraint
  c        ← liftParser this $ (parseConstraint (lexer rawc))
  c        ← analyze c
  symtab   ← use globals

  -- run the solver
  let solution = solve symtab c

  -- output solution
  liftIO $ putStrLn ""
  liftIO $ printSolution solution

  -- rinse and repeat
  loop

handler κ (Define p) = do
  this  ← view self
  pr    ← liftParser this (parsePredicate (lexer p))
  ctx   ← ask
  prty  ← analyzePred pr
  let qn = qname prty

  -- update the lexical context
  local (over (lexical.qualifier) (HM.insert (snd qn) (qn)))
    loop

handler κ (Import file) = do
  here     ← liftIO getCurrentDirectory
  let path = here </> file
  content  ← liftIO $ readFile path
  let modname = Text.pack $ takeBaseName file

  -- parse the module
  rawmod ← liftParser modname $ parseModule $ lexer content

  -- construct the type environment for the typechecker
  pretyping ← mapM (\p → do
                       let formals = sig p
                       bs ← mapM (\(n,_) → do v ← freshVar (); return (n, v)) formals
                       return (snd $ qname p, bs) ) rawmod

  defs ← local (set self modname . set typing (HM.fromList pretyping)) $ do mapM analyzePred rawmod

  let mod    = HM.fromList $ fmap (\p → (snd $ qname p , p)) defs
  let qnames = fmap qname mod

  importsMod mod

  -- update the qualifier and the symboltable
  local (over (lexical . qualifier) (HM.union qnames))
    loop

  where
handler κ Help = do
  liftIO $ putStrLn $ unlines [
    "Commands:",
    "  :def p            -- Defines a predicate p",
    "  :import f         -- Imports constraints from a file f",
    "  :help             -- Prints this help",
    "  :quit             -- Quits",
    "Constraint Syntax:",
    "  { x, .. } C       -- Extensionally quantifies variables x, .. in constraint C",
    "  C₁, C₂            -- Asserts constraints C₁ and C₂",
    "  t₁ = t₂           -- Asserts equality of terms t₁ and t₂",
    "  true              -- Asserts true",
    "  false             -- Asserts false",
    "  new x             -- Asserts that you own a node x in the graph",
    "  s₁ -[l]-> s₂      -- Asserts that you own an edge from node s₁ to node s₂ with label l in the graph",
    "  query s r as z    -- Query the graph from s with regex r as z",
    "  only(ζ, t')       -- Asserts that ζ is a singleton set containing t",
    "  every x ζ C       -- Asserts constraint C for every x in set ζ"
    ]
  loop

handler κ Quit = do
  liftIO $ exitSuccess
  loop
 
handler κ Nop =
  loop

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
  runREPL def HM.empty loop
