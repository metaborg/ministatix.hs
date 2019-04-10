module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM
import Statix.Syntax.Constraint

data Module ℓ t = Mod 
  { modname  :: Ident
  , defs     :: HashMap Ident Constraint₁ }

type Formals      = [ (Ident, Type) ]
type ModuleTyping = HashMap Ident Formals

type Symbols      = HashMap Ident (Module Ident Term₁)
type SymbolTyping = HashMap Ident ModuleTyping
type SymbolTable  = (Symbols, SymbolTyping)

-- importP :: (Predicate QName IPath Term₁) → SymbolTable → SymbolTable
-- importP p sym = HM.insert (qname $ sig p) p sym

-- importMod :: Module IPath Term₁ → SymbolTable → SymbolTable
-- importMod (Mod name defs) sym = foldl (flip importP) sym defs

-- emptyMod :: Ident → Module ℓ t
-- emptyMod m = Mod m HM.empty

-- showModuleContent :: Module ℓ t → String
-- showModuleContent mod =
--   concatMap (\p → "  (defined " ++ (show $ sig p) ++ ")\n") (HM.elems $ defs mod)
