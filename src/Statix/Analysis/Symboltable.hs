module Statix.Analysis.Symboltable where

import Data.HashMap.Strict as HM
import Control.Lens
import Statix.Syntax.Constraint

type Module       = HashMap Ident Predicate₁
type SymbolTable  = HashMap QName Predicate₁
