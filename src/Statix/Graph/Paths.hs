module Statix.Graph.Paths where

import Control.Monad.Reader
import Control.Monad.Trans

import Statix.Regex as Re
import Statix.Graph.Types

toList :: Path n l → ([(n, l)], n)
toList (End n)   = ([], n)
toList (Via e p) = let (es, end) = toList p in (e:es, end)

instance (Show n, Show l) ⇒ Show (Path n l) where

  show (End n) = show n
  show (Via (n,l) p) = show n ++ " ─⟨ " ++ show l ++ " ⟩⟶ " ++ show p
