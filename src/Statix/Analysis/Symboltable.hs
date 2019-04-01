module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM
import Statix.Syntax.Constraint

data Module ℓ t = Mod 
  { modname  :: Ident
  , defs     :: HashMap Ident (Predicate QName ℓ t) }

type SymbolTable t = HashMap QName (Predicate QName IPath t)

importP :: (Predicate QName IPath t) → SymbolTable t → SymbolTable t
importP p sym = HM.insert (qname $ sig p) p sym

importMod :: Module IPath t → SymbolTable t → SymbolTable t
importMod (Mod name defs) sym = foldl (flip importP) sym defs

emptyMod :: Ident → Module ℓ t
emptyMod m = Mod m HM.empty

showModuleContent :: Module ℓ t → String
showModuleContent mod =
  concatMap (\p → "  (defined " ++ (show $ sig p) ++ ")\n") (HM.elems $ defs mod)

type SymTab = SymbolTable Term₁ -- typer output
