module Statix.Solver.Reify where

import Data.Text

import Statix.Syntax.Constraint
import Statix.Solver.Types
import Statix.Graph.Types
import Statix.Graph.Paths as P

class Reifiable a s where
  reify :: a → STerm s

instance (Reifiable (SNode s)) s where
  reify n = SNode n

instance (Reifiable Label) s where
  reify l = SLabel l

instance (Reifiable a s) ⇒ (Reifiable [a] s) where
  reify []     = SCon (pack "Nil") []
  reify (x:xs) = SCon (pack "Cons") [reify x, reify xs]

instance (Reifiable a s, Reifiable b s) ⇒ Reifiable (a, b) s where
  reify (a, b) = SCon (pack "Pair") [reify a, reify b]

instance (Reifiable n s) ⇒ (Reifiable (Path n Label) s) where
  reify p = reify (toList p)
