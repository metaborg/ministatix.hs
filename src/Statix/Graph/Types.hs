{-# LANGUAGE UndecidableInstances #-}
module Statix.Graph.Types where

import Control.Monad.Reader
import Data.Set as Set

import Statix.Regex as Re

data Path n l = End n | Via (n , l) (Path n l)
  deriving (Eq)

{- A Graph monad interface -}
class (Monad m, Eq l, Ord n) => MonadGraph n l d m | m -> n l d where
  newNode  :: Maybe d -> m n
  newEdge  :: (n, l, n) → m ()
  getDatum :: n → m (Maybe d)
  getOutEdges :: n → m [(l, n)]

  runQuery :: n → Regex l → m [Path n l]
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
