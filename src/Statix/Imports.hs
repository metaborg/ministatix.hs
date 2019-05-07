module Statix.Imports where

import Statix.Syntax.Constraint
import Statix.Syntax.Parser
import Statix.Syntax.Lexer
import qualified Data.Graph as G
import qualified Data.Text as T
import Data.Text (Text)
import Control.Monad.Except
import Control.Monad.State
import System.FilePath


-- | Turns a module import path into a tuple of a module name
-- | and absolute file path.
resolveModule :: FilePath   -- ^ The base path (e.g., current directory or root module path).
              -> Ident      -- ^ The module name (e.g., "commons.utils").
              -> FilePath   -- ^ The module's absolute path.
resolveModule basePath modName = modPath
  where
    relModPath = getModulePath $ T.unpack modName
    modPath = simplifyPath $ dropFileName basePath </> relModPath
    getModulePath p = map repl p ++ ".stx"
      where
        repl '.' = '/'
        repl x   = x


-- | Simplifies a path by removing  "./" and "../"
-- | If any of the elements are symbolic links,
-- | this function may change where the path resolves to.
simplifyPath :: FilePath                      -- ^ The path to simplify.
             -> FilePath                      -- ^ The simplified path.
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
             -> ExceptT String IO RawModule   -- ^ IO monad wrapping either an error or the parse module.
readModuleIO modName modPath = do
  content <- liftIO $ readFile modPath
  liftEither $ readModule modName content


-- | Reads a module with the specified name and content.
readModule :: Ident                   -- ^ The name of the module.
           -> String                  -- ^ The raw content of the module.
           -> Either String RawModule -- ^ Either an error or the parsed module.
readModule modName content = do
  tokens <- lexer content
  runParser modName . parseModule $ tokens


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



type IdentStack = [Ident]
-- | Gathers the modules with the specified identifiers,
-- | and any modules they import.
gatherModules :: [Ident]                        -- ^ Set of already imported modules
              -> FilePath                       -- ^ Base directory of the project
              -> [Ident]                        -- ^ Identifiers of the modules to gather
              -> ExceptT String IO [RawModule]  -- ^ Either an error or a set of gathered modules
gatherModules imports p ix = flip evalStateT (imports, ix) $ step p
  where
    step :: FilePath -> StateT ([Ident], IdentStack) (ExceptT String IO) [RawModule]
    step p = do
      i <- pop
      (imps, _) <- get
      case i of
        Just i  | i `elem` imps -> step p -- Already imported, continue.
        Just i -> do                      -- Not yet imported:
          r <- lift $ readModuleIO i $ resolveModule p i
          let (Mod _ imports _) = r
          addImported i
          pushAll imports
          rs <- step p
          return (r:rs)
        Nothing -> return []              -- We're done!

    push :: Ident -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
    push a = state $ \(imps, xs) -> ((),(imps, a:xs))

    pushAll :: [Ident] -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
    pushAll ax = state $ \(imps, xs) -> ((), (imps, ax ++ xs))

    pop :: StateT ([Ident], IdentStack) (ExceptT String IO) (Maybe Ident)
    pop = state $ f
      where
        f (imps, (x:xs)) = ( Just x, (imps, xs))
        f (imps,     xs) = (Nothing, (imps, xs))
        
    addImported :: Ident -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
    addImported i = state $ \(imps, xs) -> ((), (i:imps, xs))
  

