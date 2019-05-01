module Statix.Imports where

import System.IO hiding (liftIO)
import System.Directory
import System.FilePath
import Data.List
import Statix.Syntax.Constraint -- (RawModule(..), ModPath)
import qualified Data.Graph as G
import Data.Map.Strict as Map hiding (map, null)
import qualified Data.HashMap.Strict as HM
import Debug.Trace
import Data.Text (pack, unpack, stripSuffix)
import Statix.Syntax.Parser
import Statix.Syntax.Lexer
import Data.Maybe (fromJust)

-- Converts an imported name into a tuple
-- of a module name, module path,
-- and whether it is relative (True) or absolute (False).
-- Examples:
--   "common.utils"   -> Import "common.utils"    "common/utils.stx" False
--   ".common.utils"  -> Import "common.utils"    "common/utils.stx" True
--   "..common.utils" -> Import "common.utils" "../common/utils.stx" True
-- NOTE: It is possible for two paths to refer to the same module
-- without Ministatix being able to deduce this. For example,
-- if the base directory is "/home/user/common/" the following two
-- imports resolve to the same file: ".utils" and "..common.utils"
-- whereas they do not in the base directory "/home/user/extra/".
-- However, Ministatix will deduce that the first module's name is "utils"
-- and find the exact duplicate module with the name "common.utils".
-- Similarly, two different relative imports ".utils" will resolve to the same module.
-- The fix is to use the base path to determine the absolute module name (TBD).


toModulePath :: ModPath -> (Ident, ModPath, Bool)
toModulePath = toModulePath_ . unpack

toModulePath_ :: String -> (Ident, ModPath, Bool)
toModulePath_ ('.':p) = (((pack . getModuleName_) p), ((pack . getModulePath_) p),  True)
toModulePath_ p       = (((pack . getModuleName_) p), ((pack . getModulePath_) p), False)

getModuleName :: ModPath -> Ident
getModuleName = pack . getModuleName_ . unpack

getModuleName_ :: String -> String
getModuleName_ ('.':n) = getModuleName_ n
getModuleName_ n       = n

getModulePath :: ModPath -> ModPath
getModulePath = pack . getModulePath_ . unpack

getModulePath_ :: String -> String
getModulePath_ ('.':p) = "../" ++ getModulePath_ p
getModulePath_ p       = map replaceModulePathChar p ++ ".stx"

replaceModulePathChar :: Char -> Char
replaceModulePathChar '.' = '/'
replaceModulePathChar x   = x

-- Import
-- * name
-- * path
-- * whether the path is relative (True) or absolute (False)
-- data Import = Import Ident ModPath Bool deriving (Show)

-- Import algorithm
-- We have a worklist with modules
-- Until the worklist is empty, for each module in the worklist:
-- 1) Pop and add to parsed modules set
-- 2) Parse
-- 3) Gather imports
-- For each import from the module,
-- if it is NOT in the parsed modules set:
-- add it to the worklist.
--
-- Invariant: the worklist is empty, all modules are parsed
-- and their imports gathered.
--
-- 1) Build a graph of modules, where A -> B implies B depends on A
-- (i.e., the inverse of what you might expect).
-- 2) Get the topological sort of the graph (see Data.Graph.topSort)
-- 3) Load modules in topological order.

-- Turns a module import path into a module name and absolute file path
-- This takes the base directory, current directory, and module import.
resolveModule :: FilePath -> FilePath -> ModPath -> (Ident, FilePath)
resolveModule absp relp modp = case toModulePath modp of
  -- FIXME: Determine the module name from the resulting path relative to the base path
  (modName, modPath,  True) -> (modName, relp </> unpack modPath)
  (modName, modPath, False) -> (modName, absp </> unpack modPath)


modnameFromPath :: FilePath -> FilePath -> Either String Ident
modnameFromPath basepath modpath = do
  relpath <- ensureRelative $ makeRelative basepath modpath
  return $ pack . concat $ intersperse "." $ onLast stripStxSuffix $ splitDirectories relpath

stripStxSuffix :: FilePath -> FilePath
stripStxSuffix s = unpack (fromJust $ stripSuffix ".stx" $ pack s)

ensureRelative :: FilePath -> Either String FilePath
ensureRelative p = case isRelative p of
  True  -> Right p
  False -> Left ("Path '" ++ p ++ "' points to a location outside the base directory.")

onLast :: (a -> a) -> [a] -> [a]
onLast f (x:y:xs) = (x : onLast f (y:xs))
onLast f [x]      = [f x]
onLast _ []       = []

-- modnameFromPath :: FilePath -> FilePath -> Either String Ident
-- modnameFromPath basepath modpath =
--   let relpath = makeRelative basepath modpath in
--     case isRelative relpath of
--       -- TODO: stripSuffix ".stx" from the last element
--       -- returns nothing if suffix is not present (error)
--       True  -> Right $ pack . concat $ intersperse "." $ splitDirectories relpath
--       False -> Left ("Path '" ++ relpath ++ "' points to a location outside the base directory.")

-- Reads a module with the specified name from the specified path
readModuleIO :: Ident -> FilePath -> IO (Either String RawModule)
readModuleIO modName modPath = do
  content <- readFile modPath
  return $ readModule modName content

-- Reads a module with the specified name and content
readModule :: Ident -> String -> Either String RawModule
readModule modName content =
  let tokens = lexer content in
  (tokens >>= runParser modName . parseModule)

-- importModule :: SymbolTable -> RawModule -> ()
-- importModule symtab rawmod =
--   -- Typecheck the module
--   let mod = analyze symtab rawmod

--   -- Import the typechecked module into the symboltable
--   importMod modName mod

-- Produces a topological sort of a list of modules
-- according to their import dependencies.
-- The returned list is from dependee to depender.
moduleTopSort :: [RawModule] -> [RawModule]
moduleTopSort modules =
  let edges = [(mod, name, map getModuleName imports) | mod@(Mod name imports _) <- modules ] in
  let (graph, vertexToNode, _) = G.graphFromEdges edges in
  let sorted = (reverse . G.topSort) graph in
    [mod | (mod, _, _) <- map vertexToNode sorted]

