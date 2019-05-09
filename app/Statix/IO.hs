module Statix.IO where

import qualified Data.Graph as G
-- import Data.HashMap.Strict as HM
-- import Data.Default
import Data.List (intercalate)

import Control.Monad.State
import Control.Monad.Except
import Control.Lens

import System.Directory (doesFileExist)
import System.FilePath

import Statix.Syntax
import Statix.Repl.Types (REPL, imports, globals, importMod)
import Statix.Analysis (analyze)
import Statix.Analysis.Symboltable
import Statix.Syntax.Parser (parseModule)
import Statix.Syntax.Surface (desugarMod)

-- | Loads a module, and any modules on which it depends.
loadModule :: [FilePath]                              -- ^ The root paths against which imports are resolved.
           -> Ident                                   -- ^ The name of the module.
           -> ExceptT String REPL Module              -- ^ The loaded module.
loadModule rootpaths name = do
  path <- mapExceptT liftIO $ resolveModule rootpaths name
  loadModuleFromFile rootpaths name path


-- | Loads a module from file, and any modules on which it depends.
loadModuleFromFile :: [FilePath]                      -- ^ The root paths against which imports are resolved.
                   -> Ident                           -- ^ The name of the module.
                   -> FilePath                        -- ^ The path to the module.
                   -> ExceptT String REPL Module      -- ^ The loaded module.
loadModuleFromFile rootpaths name path = do
  content <- liftIO $ readFile path
  loadModuleFromText rootpaths name content


-- | Loads a module from text, and any modules on which it depends.
loadModuleFromText :: [FilePath]                      -- ^ The root paths against which imports are resolved.
                   -> Ident                           -- ^ The name of the module.
                   -> String                          -- ^ The textual content of the module.
                   -> ExceptT String REPL Module      -- ^ The loaded module.
loadModuleFromText rootpaths name content = do
  -- Gather the modules, then sort them topologically
  rawmod  <- liftEither $ desugarMod <$> parseModule name content
  imps    <- use imports
  let resolver i = if (i == name) then return rawmod else readRawModule rootpaths i
  allrawmods <- mapExceptT liftIO $ gatherModules imps resolver [name]
  let sortedrawmods = moduleTopSort allrawmods
  -- Typecheck and import the module into the symbol table
  symtab <- use globals
  modsWithNames <- mapM (analyzeAndImport symtab) sortedrawmods
  return $ snd $ head $ filter (\(n, _) -> n == name) modsWithNames
    where
      analyzeAndImport symtab rawmod@(Mod name _ _) = do
        -- Typecheck the module
        mod <- withExceptT show $ analyze symtab rawmod
        -- Import the typechecked module into the symboltable
        lift $ importMod name mod
        return (name, mod)


-- | Reads a single raw module.
readRawModule :: [FilePath]                           -- ^ The root paths against which imports are resolved.
              -> Ident                                -- ^ The name of the module.
              -> ExceptT String IO RawModule₀         -- ^ The loaded module.
readRawModule rootpaths name = do
  path <- mapExceptT liftIO $ resolveModule rootpaths name
  rawmod <- readRawModuleFromFile name path
  return rawmod


-- | Reads a single raw module from the specified path.
readRawModuleFromFile :: Ident                        -- ^ The name of the module.
                      -> FilePath                     -- ^ The path to the module.
                      -> ExceptT String IO RawModule₀ -- ^ The loaded module.
readRawModuleFromFile name path = do
  content <- liftIO $ readFile path
  readRawModuleFromText name content


-- | Reads a single raw module from the specified content.
readRawModuleFromText :: Ident                        -- ^ The name of the module.
                      -> String                       -- ^ The textual content of the module.
                      -> ExceptT String IO RawModule₀  -- ^ The loaded module.
readRawModuleFromText name content = liftEither $ desugarMod <$> parseModule name content


-- | Resolves a module to its absolute path, if any.
resolveModule :: [FilePath]                           -- ^ The root paths.
              -> Ident                                -- ^ The module name.
              -> ExceptT String IO FilePath           -- ^ The module's absolute path, if found.
resolveModule rootpaths name = do
  let paths = fmap (flip getModulePath name) rootpaths
  foundpaths <- liftIO $ filterM doesFileExist paths
  case foundpaths of
    [path] -> return path
    []     -> throwError $ "Module " ++ name ++ " not found at: " ++ (intercalate ", " paths)
    mpaths -> throwError $ "Module " ++ name ++ " found in multiple places: " ++ (intercalate ", " mpaths)
  where
    -- | Gets the absolute path of a module from its module name and root path.
    getModulePath :: FilePath                             -- ^ The root path.
                  -> Ident                                -- ^ The module name.
                  -> FilePath                             -- ^ The module's (expected) absolute path.
    getModulePath basePath name = abspath
      where
        relpath = buildModulePath $ name
        abspath = simplifyPath $ dropFileName basePath </> relpath
        buildModulePath p = fmap repl p ++ ".mstx"
          where
            repl '/'  = '_'
            repl '\\' = '_'
            repl '.'  = '/'
            repl x    = x


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


type IdentStack = [Ident]
-- | Gathers the modules with the specified identifiers,
-- | and any modules they import.
gatherModules :: [Ident]                                  -- ^ Set of already imported modules
              -> (Ident -> ExceptT String IO RawModule₀)  -- ^ Function that provides the raw module with the specified name.
              -> [Ident]                                  -- ^ Identifiers of the modules to gather
              -> ExceptT String IO [RawModule₀]           -- ^ Either an error or a set of gathered modules
gatherModules imports resolver ix = flip evalStateT (imports, ix) $ step resolver
  where
    step :: (Ident -> ExceptT String IO RawModule₀)
         -> StateT ([Ident], IdentStack) (ExceptT String IO) [RawModule₀]
    step resolver = do
      i <- pop
      (imps, _) <- get
      case i of
        Just i  | i `elem` imps -> do
          step resolver  -- Already imported, continue.
        Just i -> do     -- Not yet imported:
          r <- lift $ resolver i
          let (Mod _ imports _) = r
          addImported i
          pushAll imports
          rs <- step resolver
          return (r:rs)
        Nothing -> do
          return []      -- We're done!

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


-- | Produces a topological sort of a list of modules
-- | according to their import dependencies.
-- | The returned list is from dependee to depender.
moduleTopSort :: [RawModule₀]    -- ^ The list of modules to sort.
              -> [RawModule₀]    -- ^ The sorted list of modules.
moduleTopSort modules =
  let edges = [(mod, name, imports) | mod@(Mod name imports _) <- modules ] in
  let (graph, vertexToNode, _) = G.graphFromEdges edges in
  let sorted = (reverse . G.topSort) graph in
    [mod | (mod, _, _) <- map vertexToNode sorted]
