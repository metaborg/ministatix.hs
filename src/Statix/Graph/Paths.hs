module Statix.Graph.Paths where

data Path n l = End n | Via (n , l) (Path n l)
  deriving (Show, Eq)

toList :: Path n l → ([(n, l)], n)
toList (End n)   = ([], n)
toList (Via e p) = let (es, end) = toList p in (e:es, end)
