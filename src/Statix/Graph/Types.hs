module Statix.Graph.Types where

import Statix.Regex as Re

data Path n l t = End n | Via (n, l, Maybe t) (Path n l t)
  deriving (Eq)

type CriticalEdge n l = (n , Regex l)

{- A Graph monad interface -}
class (Monad m, Eq l, Ord n) => MonadGraph n l d m | m -> n l d where
  newNode  :: Maybe d -> m n
  newEdge  :: (n, l, Maybe d, n) → m ()
  getDatum :: n → m (Maybe d)
  setDatum :: n → d → m ()
  getOutEdges :: n → m [(l, Maybe d, n)]
