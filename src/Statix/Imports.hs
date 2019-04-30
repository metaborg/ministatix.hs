module Statix.Imports where

import Statix.Syntax.Constraint -- (RawModule(..), ModPath)
import qualified Data.Graph as G
import Data.Map.Strict as Map hiding (map, null)
import qualified Data.HashMap.Strict as HM
import Debug.Trace
import Data.Text hiding (unlines, map, concatMap)

-- Converts an imported name into a tuple
-- of a module name, module path,
-- and whether it is relative (True) or absolute (False).
-- Examples:
--   "common.utils"   -> Import "common.utils"    "common/utils.stx" False
--   ".common.utils"  -> Import "common.utils"    "common/utils.stx" True
--   "..common.utils" -> Import "common.utils" "../common/utils.stx" True
-- NOTE: It is possible for two paths to refer to the same module
-- without Ministatix being able to dedice this. For example,
-- if the base directory is "/home/user/common/" the following two
-- imports resolve to the same file: ".utils" and "..common.utils"
-- whereas they do not in the base directory "/home/user/extra/".
-- However, Ministatix will deduce that the first module's name is "utils"
-- and find the exact duplicate module with the name "common.utils".
-- In other words, prefer absolute paths.

toModulePath :: ModPath -> Import
toModulePath = toModulePath_ . unpack

toModulePath_ :: String -> Import
toModulePath_ ('.':p) = Import ((pack . getModuleName_) p) ((pack . getModulePath_) p) True
toModulePath_ p       = Import ((pack . getModuleName_) p) ((pack . getModulePath_) p) False

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
data Import = Import Ident ModPath Bool deriving (Show)

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

-- vertexToMod :: 

moduleTopSort :: [RawModule] -> [RawModule]
moduleTopSort modules =
  -- Create a map from module names to modules
  let moduleMap = HM.fromList $ map (\m@(Mod name _ _) -> (name, m)) modules in
  let edges = map (\m@(Mod name imports _) -> (m, name, map getModuleName imports)) modules in
  let (graph, vertexToNode, keyToVertex) = G.graphFromEdges edges in
  let sorted = (G.topSort . G.transposeG) graph in
    map ((\(x, _, _) -> x) . vertexToNode) sorted
  
  