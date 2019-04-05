module Statix.Graph.Types where

import Control.Monad.Reader
import Data.Set as Set
import Data.Map as Map

import Statix.Regex as Re

data Path n l = End n | Via (n , l) (Path n l)
  deriving (Eq)

type CriticalEdge n l = (n , Regex l)

{- A Graph monad interface -}
class (Monad m, Eq l, Ord n) => MonadGraph n l d m | m -> n l d where
  newNode  :: Maybe d -> m n
  newEdge  :: (n, l, n) → m ()
  getDatum :: n → m (Maybe d)
  getOutEdges :: n → m [(l, n)]

-- | Find reachable nodes in the graph over a regex.
-- Together with the regex derivative in that node
findReachable :: (Ord l, MonadGraph n l d m) ⇒ n → Regex l → m (Map n (Regex l))
findReachable n re = _find n re Set.empty
  where
    _find n re vis
      | Re.empty re = return Map.empty
      | otherwise   = do
       -- check if we visited this node yet on the path here
       if Set.member n vis
         then return Map.empty
         else do
           -- get the edges out of here
           es ← getOutEdges n
           reachables ← Map.unionsWith RAlt <$> mapM (\(l, m) → _find m (Re.match l re) vis) es 
           return (Map.insertWith RAlt n re reachables)

-- | Find regular paths in the graph
runQuery :: (MonadGraph n l d m) ⇒ n → Regex l → m [Path n l]
runQuery n re = _resolve n re Set.empty
  where
    _resolve n re vis
      | Re.empty re = return []
      | otherwise   = do
       -- check if we visited this node yet on the path here
       if Set.member n vis
         then return []
         else do
           -- get the edges out of here
           es ← getOutEdges n
           -- calculate the paths out of here
           pss ← mapM (\ (l , tgt) → do
                     ps ← _resolve tgt (Re.match l re) (Set.insert n vis)
                     return (fmap (Via (n , l)) ps)
                   ) es
           let ps = concat pss
           -- add the loop if it exists
           return (if Re.matchε re then (End n : ps) else ps)
