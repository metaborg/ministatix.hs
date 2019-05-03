module Statix.Imports where


-- import Data.List (foldl', foldl)
import System.IO hiding (liftIO)
import System.Directory
import System.FilePath
import Data.List
import Statix.Syntax.Constraint -- (RawModule(..), ModPath)
import qualified Data.Graph as G
import Data.Map.Strict as Map hiding (map, null, foldl', foldl)
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



-- | Turns a module import path into a tuple of a module name
-- | and absolute file path.
resolveModule :: FilePath   -- ^ The base path (e.g., current directory or root module path).
              -> Ident      -- ^ The module name (e.g., "commons.utils").
              -> FilePath   -- ^ The module's absolute path.
resolveModule basePath modName = modPath
  where
    relModPath = getModulePath $ unpack modName
    modPath = simplifyPath $ dropFileName basePath </> relModPath
    getModulePath p = map repl p ++ ".stx"
      where
        repl '.' = '/'
        repl x   = x


-- | Simplifies a path by removing  "./" and "../"
-- | If any of the elements are symbolic links,
-- this function may change where the path resolves to.
simplifyPath :: FilePath -> FilePath
simplifyPath p = joinPath $ reverse newDirs where
  newDirs = foldl step [] (splitPath p)

  step acc c | dropTrailingPathSeparator c == "." = case acc of
    []                         -> c:acc
    _                          -> acc
  step acc c | dropTrailingPathSeparator c == ".." = case acc of
    []                         -> c:acc    -- Prepend "../" to the empty list.
    [[s]]  | isPathSeparator s -> acc      -- Keep the path absolute
    (h:ts) | dropTrailingPathSeparator h ==  "." -> c:ts     
           | dropTrailingPathSeparator h == ".." -> c:acc
           | otherwise         -> ts
  step acc c              = c:acc


-- | Reads a module with the specified name from the specified path
readModuleIO :: Ident                         -- ^ The name of the module.
             -> FilePath                      -- ^ The path to the module.
             -> IO (Either String RawModule)  -- ^ IO monad wrapping either an error or the parse module.
readModuleIO modName modPath = do
  content <- readFile modPath
  return $ readModule modName content


-- | Reads a module with the specified name and content.
readModule :: Ident                   -- ^ The name of the module.
           -> String                  -- ^ The raw content of the module.
           -> Either String RawModule -- ^ Either an error or the parsed module.
readModule modName content =
  let tokens = lexer content in
  (tokens >>= runParser modName . parseModule)


-- | Produces a topological sort of a list of modules
-- | according to their import dependencies.
-- | The returned list is from dependee to depender.
moduleTopSort :: [RawModule]    -- ^ The list of modules to sort.
              -> [RawModule]    -- ^ The sorted list of modules.
moduleTopSort modules =
  let edges = [(mod, name, imports) | mod@(Mod name imports _) <- modules ] in
  let (graph, vertexToNode, _) = G.graphFromEdges edges in
  let sorted = (reverse . G.topSort) graph in
    [mod | (mod, _, _) <- map vertexToNode sorted]

