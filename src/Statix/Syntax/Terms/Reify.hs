{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Statix.Syntax.Terms.Reify where

import Control.Unification

import Statix.Syntax.Constraint
import Statix.Graph
import Statix.Graph.Types
import Statix.Graph.Paths as P

class Reifiable a n r where
  reify :: a → UTerm (TermF n) r

instance (Reifiable n n r) where
  reify n = Node n

instance (Reifiable Label n r) where
  reify l = Label l

instance (Reifiable a n r) ⇒ (Reifiable [a] n r) where
  reify []     = Con "Nil" []
  reify (x:xs) = Con "Cons" [reify x, reify xs]

instance (Reifiable a n r, Reifiable b n r) ⇒ Reifiable (a, b) n r where
  reify (a, b) = Con "Pair" [reify a, reify b]

instance (Reifiable n n r) ⇒ (Reifiable (Path n Label) n r) where
  reify p = reify (P.toList p)
