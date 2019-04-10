module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM
import Control.Lens
import Statix.Syntax.Constraint

type Module       = HashMap Ident Predicate₁
type SymbolTable  = HashMap QName Predicate₁

importP :: Predicate₁ → SymbolTable → SymbolTable
importP p sym = HM.insert (qname p) p sym

importMod :: Module → SymbolTable → SymbolTable
importMod mod sym = foldl (flip importP) sym mod

-- emptyMod :: Ident → Module ℓ t
-- emptyMod m = Mod m HM.empty

-- showModuleContent :: Module ℓ t → String
-- showModuleContent mod =
--   concatMap (\p → "  (defined " ++ (show $ sig p) ++ ")\n") (HM.elems $ defs mod)
