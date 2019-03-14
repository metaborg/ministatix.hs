module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM
import Statix.Syntax.Constraint

data Module = Mod 
  { modname  :: ModName
  , defs     :: HashMap RawName (Predicate QName) }

type SymbolTable      = HashMap QName (Predicate QName)

importP :: Predicate QName → SymbolTable → SymbolTable
importP p sym = HM.insert (qname $ sig p) p sym

importMod :: Module → SymbolTable → SymbolTable
importMod (Mod name defs) sym = foldl (flip importP) sym defs

emptyMod :: ModName → Module
emptyMod m = Mod m HM.empty

showModuleContent :: Module → String
showModuleContent mod = concatMap (\p → "  (defined " ++ (show $ sig p) ++ ")\n") (HM.elems $ defs mod)
