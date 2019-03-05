module Statix.Graph
  ( IntGraphEdge(..)
  , IntGraphNode(..)
  , IntGraph(..)
  ) where

import Data.IntMap
import Statix.Syntax.Constraint

data IntGraphEdge l = IntEdge l Int
  deriving (Show)

data IntGraphNode l d = IntNode
  { id    :: Int
  , edges :: [IntGraphEdge l]
  , datum :: d
  } deriving (Show)

type IntGraph l d = IntMap (IntGraphNode l d)
