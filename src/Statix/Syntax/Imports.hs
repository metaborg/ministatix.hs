module Statix.Syntax.Imports where

-- Converts an imported name into a tuple
-- of a module name, module path,
-- and whether it is relative (True) or absolute (False).
-- Examples:
--   "common.utils"   -> ("common.utils",    "common/utils.stx", False)
--   ".common.utils"  -> ("common.utils",    "common/utils.stx", True)
--   "..common.utils" -> ("common.utils", "../common/utils.stx", True)
toModulePath :: String -> (String, String, Bool)
toModulePath ('.':p) = (getModuleName p, getModulePath p, True)
toModulePath p       = (getModuleName p, getModulePath p, False)

getModuleName :: String -> String
getModuleName ('.':n) = n
getModuleName n       = n

getModulePath :: String -> String
getModulePath ('.':p) = "../" ++ getModulePath p
getModulePath p       = map replaceModulePathChar p ++ ".stx"

replaceModulePathChar :: Char -> Char
replaceModulePathChar '.' = '/'
replaceModulePathChar x   = x
