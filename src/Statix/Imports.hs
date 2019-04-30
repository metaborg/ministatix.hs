module Statix.Imports where

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

