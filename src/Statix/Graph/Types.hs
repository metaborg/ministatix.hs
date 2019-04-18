module Statix.Graph.Types where

import Statix.Regex as Re

data Path n l = End n | Via (n , l) (Path n l)
  deriving (Eq)

type CriticalEdge n l = (n , Regex l)

{- A Graph monad interface -}
class (Monad m, Eq l, Ord n) => MonadGraph n l d m | m -> n l d where
  newNode  :: Maybe d -> m n
  newEdge  :: (n, l, n) → m ()
  getDatum :: n → m (Maybe d)
  setDatum :: n → d → m ()
  getOutEdges :: n → m [(l, n)]
