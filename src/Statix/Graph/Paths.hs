module Statix.Graph.Paths where

data Path n l = End n | Via (n , l) (Path n l)
  deriving (Show, Eq)
