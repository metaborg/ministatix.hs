module Statix.Imports where

  import Statix.Syntax.Constraint (RawModule)
  import qualified Data.Graph as G
  import qualified Data.HashMap.Strict as M
  
  -- Converts an imported name into a tuple
  -- of a module name, module path,
  -- and whether it is relative (True) or absolute (False).
  -- Examples:
  --   "common.utils"   -> Import "common.utils"    "common/utils.stx" False
  --   ".common.utils"  -> Import "common.utils"    "common/utils.stx" True
  --   "..common.utils" -> Import "common.utils" "../common/utils.stx" True
  toModulePath :: String -> Import
  toModulePath ('.':p) = Import (getModuleName p) (getModulePath p) True
  toModulePath p       = Import (getModuleName p) (getModulePath p) False
  
  getModuleName :: String -> String
  getModuleName ('.':n) = n
  getModuleName n       = n
  
  getModulePath :: String -> String
  getModulePath ('.':p) = "../" ++ getModulePath p
  getModulePath p       = map replaceModulePathChar p ++ ".stx"
  
  replaceModulePathChar :: Char -> Char
  replaceModulePathChar '.' = '/'
  replaceModulePathChar x   = x
  
  -- Import
  -- * name
  -- * path
  -- * whether the path is relative (True) or absolute (False)
  data Import = Import String String Bool deriving (Show)
  
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
  
  -- moduleTopSort ::[RawModule] -> [RawModule]
  -- moduleTopSort mods =
  --   -- Create a map from module names to modules
  --   let modules = M.fromList
    -- G.graphFromEdges [
  
    -- ]
    
  