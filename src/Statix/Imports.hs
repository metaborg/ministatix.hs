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
import Control.Monad.Except
import Data.Either (fromRight)
import Control.Monad.State
import Data.Text (Text)
import qualified Data.Text as T
-- import Control.Error.Safe (tryRight)


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
             -> ExceptT String IO RawModule   -- ^ IO monad wrapping either an error or the parse module.
readModuleIO modName modPath = do
  content <- liftIO $ readFile modPath
  liftEither $ readModule modName content

-- -- | Reads a module with the specified name from the specified path
-- readModuleIO :: Ident                         -- ^ The name of the module.
--              -> FilePath                      -- ^ The path to the module.
--              -> IO (Either String RawModule)  -- ^ IO monad wrapping either an error or the parse module.
-- readModuleIO modName modPath = do
--   content <- readFile modPath
--   return $ readModule modName content


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

-- -- | Imports the module with the specified name and path,
-- -- | and any modules on which it depends.
-- importModuleFromFile :: [Ident]
--                      -> Ident
--                      -> FilePath
--                      -> IO Either String [Ident]
-- importModule existingImports mod = do
--   return existingImports

-- importModule :: [Ident]
--              -> Ident
--              -> String
--              -> IO Either String [Ident]
-- importModule


-- add the identifier to the worklist
-- 1) pop an identifier from the worklist
-- if the identifier is in the REPLState _imports,
-- we assume it has been parsed, analayzed, and added to the symbol table,
-- and that this is also the case for the modules on which it depends (imports).
-- so then we skip this one.
-- otherwise:
-- 2) find and parse the module
-- 3) add it to the list of modules
-- 4) add its imports to the worklist
-- when the worklist is empty, we have a list of modules
-- 6) order the modules topologically
-- 7) for each module in the list:
-- 7a) analyze
-- 7b) add to symbol table (importMod)
-- the list of modules is now empty
-- gatherModules :: [Ident] -> Ident -> IO [RawModule]
-- Recursive is not going to work: there may be cycles in the import graph
-- gatherModules imported modName = do
--   -- if modName `elem` imported then
--   here       <- getCurrentDirectory
--   let modPath = resolveModule here modName
--   -- FIXME: How to deal with IO Either neatly?
--   r <- readModuleIO modName modPath
--   let rawmod = fromRight (Mod "" [] []) r

--   rm <- gatherModules imported 

--   return []
  -- r' <- fromRight rm r
  -- case r of
  --   Left err                -> return $ []
  --   Right (Mod _ imports _) -> return $ []
-- gatherModules :: [Ident] -> Ident -> IO (Either String [RawModule])
-- gatherModules imported modName = do
--   -- if modName `elem` imported then
--   here       <- getCurrentDirectory
--   let modPath = resolveModule here modName
--   r <- readModuleIO modName modPath
--   case r of
--     Left err                -> return $ Left err
--     Right (Mod _ imports _) -> return $ Left "ss"

-- handleIOErrors :: Either String a -> IO a
-- handleIOErrors (Right a)  = return a
-- handleIOErrors (Left err) = runExceptT $ do
--   ExceptT $ putStrLn err
  -- loop

type IdentStack = [Ident]
-- -- pop :: StateT IdentStack (ExceptT String IO) Ident
-- -- pop = state $ \(x:xs) -> (x,xs)
-- push :: Ident -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
-- push a = state $ \(imps, xs) -> ((),(imps, a:xs))
-- pushAll :: [Ident] -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
-- pushAll ax = state $ \(imps, xs) -> ((), (imps, ax ++ xs))
-- pop :: StateT ([Ident], IdentStack) (ExceptT String IO) (Maybe Ident)
-- pop = state $ f
--   where
--     f (imps, (x:xs)) = ( Just x, (imps, xs))
--     f (imps,     xs) = (Nothing, (imps, xs))
-- addImported :: Ident -> StateT ([Ident], IdentStack) (ExceptT String IO) ()
-- addImported i = state $ \(imps, xs) -> ((), (i:imps, xs))

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
  

